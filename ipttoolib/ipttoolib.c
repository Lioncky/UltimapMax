#define PRINT_DETAIL 0
#include <Windows.h>
#include <dbghelp.h>
#include <stdio.h>
#include <stdint.h>

#include <intel-pt.h>
#include <libipt.h>
#pragma comment(lib, "dbghelp")
#pragma comment(lib, "D:\\Cod\\winipt\\x64\\Release\\libipt.lib")
#define logpath "C:\\Users\\Administrator\\Desktop\\ipt_tool.log"
#define IPT_TOOL_USE_MTC_TIMING_PACKETS     0x01
#define IPT_TOOL_USE_CYC_TIMING_PACKETS     0x02
#define IPT_TOOL_TRACE_KERNEL_MODE          0x04
#define IPT_TOOL_TRACE_ALL_MODE             0x08

#define IPT_TOOL_VALID_FLAGS                \
    (IPT_TOOL_USE_MTC_TIMING_PACKETS |      \
     IPT_TOOL_USE_CYC_TIMING_PACKETS |      \
     IPT_TOOL_TRACE_KERNEL_MODE |           \
     IPT_TOOL_TRACE_ALL_MODE)

typedef enum _IPT_TL_ACTION
{
	IptTlStartTrace,
	IptTlStopTrace,
	IptTlGetTrace,
	IptTlQueryTrace,
	IptTlPauseTrace,
	IptTlResumeTrace,
	IptTlConfigureFilter,
	IptTlQueryFilter,
	IptTlQueryTraceStop,
} IPT_TL_ACTION;


// ============================================================
// Global
// ============================================================

// DLL 注入 -1 就是当前进程 pseudo handle。
// 不需要 OpenProcess，也不要 CloseHandle。
static HANDLE g_hProcess = (HANDLE)-1;

static volatile LONG g_running = 1;

static BOOL g_tracing = FALSE;

static BOOL g_symInit = FALSE;

extern void clean();
extern void sumup();
extern void enter(uintptr_t _to);
static PBYTE g_end = FALSE;
#define _ImageSize(_)  

static void InitSymbols()
{
	if (g_symInit) return; // 系统 DLL 的符号需要 symsrv.dll 放在 dbghelp.dll 旁边
	SymSetOptions(SYMOPT_UNDNAME | SYMOPT_DEFERRED_LOADS | SYMOPT_LOAD_LINES);
	SymInitialize(GetCurrentProcess(),
		"srv*C:\\symbols*https://msdl.microsoft.com/download/symbols", TRUE);
	g_symInit = TRUE;

}

void Symbolize(uint64_t addr, char* out, size_t cap)
{
	char modName[MAX_PATH] = "?";
	HMODULE hm = NULL;

	if (GetModuleHandleExA(
		GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS |
		GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT,
		(LPCSTR)addr, &hm))
	{
		char full[MAX_PATH];
		GetModuleFileNameA(hm, full, MAX_PATH);
		const char* base = strrchr(full, '\\');
		lstrcpyA(modName, base ? base + 1 : full);
	}
	else
	{
		hm = NULL;
	}

	char buf[sizeof(SYMBOL_INFO) + 256];
	SYMBOL_INFO* sym = (SYMBOL_INFO*)buf;
	memset(sym, 0, sizeof(SYMBOL_INFO));
	sym->SizeOfStruct = sizeof(SYMBOL_INFO);
	sym->MaxNameLen = 255;
	DWORD64 disp = 0;

	if (SymFromAddr(GetCurrentProcess(), addr, &disp, sym))
		sprintf_s(out, cap, disp ? "%s!%s+0x%llX" : "%s!%s", modName, sym->Name, disp);
	else if (hm)
		disp = (DWORD64)addr - (DWORD64)hm,
		sprintf_s(out, cap, disp ? "%s+0x%llX" : "%s", modName, addr - (uint64_t)hm);
	else
		sprintf_s(out, cap, "0x%llX", addr);
}

// ------------------------------------------------------------
// libipt 的内存读取回调：直接读本进程内存
// ------------------------------------------------------------
static int ReadMemCb(uint8_t* buffer, size_t size,
	const struct pt_asid* asid, uint64_t ip, void* context)
{
	UNREFERENCED_PARAMETER(asid);
	UNREFERENCED_PARAMETER(context);

	SIZE_T n = 0;
	if (!ReadProcessMemory(g_hProcess, (LPCVOID)ip, buffer, size, &n) || n == 0)
		return -pte_nomap;
	return (int)n;
}

static void GetCpuInfo(struct pt_cpu* cpu)
{
	int r[4];
	__cpuid(r, 1);
	unsigned eax = (unsigned)r[0];

	cpu->vendor = pcv_intel;     // AMD 没有 PT，这里默认 Intel
	cpu->family = (eax >> 8) & 0xF;
	cpu->model = (eax >> 4) & 0xF;
	cpu->stepping = eax & 0xF;
	if (cpu->family == 0xF)
		cpu->family += (eax >> 20) & 0xFF;
	if (cpu->family == 6 || cpu->family == 0xF)
		cpu->model += ((eax >> 16) & 0xF) << 4;
}

// ------------------------------------------------------------
// 解码并打印调用栈
// ------------------------------------------------------------
#define MAX_SHADOW  4096
#define MAX_PRINT   3000     // 调用日志最多打印多少行

static void DumpCallStack(const BYTE* trace, DWORD size, DWORD ringOff)
{
	InitSymbols();

	// ---- 1. 线性化环形缓冲区 ----
	BYTE* linear = (BYTE*)malloc(size);
	if (!linear) return;

	if (ringOff > 0 && ringOff < size)
	{
		memcpy(linear, trace + ringOff, size - ringOff);
		memcpy(linear + (size - ringOff), trace, ringOff);
	}
	else
	{
		memcpy(linear, trace, size);
	}

	// ---- 2. 配置解码器 ----
	struct pt_config cfg;
	pt_config_init(&cfg);
	cfg.begin = linear;
	cfg.end = linear + size;
	GetCpuInfo(&cfg.cpu);
	pt_cpu_errata(&cfg.errata, &cfg.cpu);

	struct pt_image* img = pt_image_alloc("self");
	pt_image_set_callback(img, ReadMemCb, NULL);

	struct pt_insn_decoder* dec = pt_insn_alloc_decoder(&cfg);
	if (!dec) { printf("  [-] pt_insn_alloc_decoder failed\n"); free(linear); return; }
	pt_insn_set_image(dec, img);

	// ---- 3. 解码 ----
	uint64_t* shadow = malloc(MAX_SHADOW);
	int sp = 0;
	uint64_t totalCalls = 0, printed = 0;
	int pendingKind = 0;           // 1 = 刚执行 call, 2 = 刚执行 ret
	uint64_t pendingCaller = 0, pendingRet = 0;
	char s1[512], s2[512];

	for (;;)
	{
		int status = pt_insn_sync_forward(dec);
		if (status < 0) break;               // pte_eos：结束

		pendingKind = 0;

		for (;;)
		{
			while (status & pts_event_pending)
			{
				struct pt_event ev;
				status = pt_insn_event(dec, &ev, sizeof(ev));
				pendingKind = 0;             // 事件(异步跳转/中断)会打断 call/ret 配对
				if (status < 0) break;
			}
			if (status < 0) break;

			struct pt_insn insn;
			memset(&insn, 0, sizeof(insn));
			status = pt_insn_next(dec, &insn, sizeof(insn));

			if (insn.iclass != ptic_error)
			{

				// Boost Range
				if (pendingCaller > g_end || insn.ip > g_end)
				{
				}
				else if (pendingKind == 1)
				{
					// 这条指令的 ip 就是 call 的目标
					totalCalls++;
					if (printed < MAX_PRINT)
					{
						Symbolize(pendingCaller, s1, sizeof(s1));
						Symbolize(insn.ip, s2, sizeof(s2));
						int indent = sp * 2; if (indent > 60) indent = 60;
						
						#if  PRINT_DETAIL
						printf("  %*s%s  ->  %s\n", indent, "", s1, s2);
						#endif

						enter(insn.ip);
						printed++;
					}
					if (sp < MAX_SHADOW) shadow[sp++] = pendingRet;
				}
				else if (pendingKind == 2)
				{
					// insn.ip 是 ret 落地的地址，在影子栈里找匹配项(兼容异常/longjmp)
					for (int i = sp; i > 0; i--)
					{
						if (shadow[i - 1] == insn.ip) { sp = i - 1; break; }
					}
				}
				pendingKind = 0;

				if (insn.iclass == ptic_call || insn.iclass == ptic_far_call)
				{
					pendingKind = 1;
					pendingCaller = insn.ip;
					pendingRet = insn.ip + insn.size;
				}
				else if (insn.iclass == ptic_return || insn.iclass == ptic_far_return)
				{
					pendingKind = 2;
				}
			}

			if (status < 0) break;           // 出错 → 回到外层重新 sync
		}
	}

	printf("  call 总数: %llu (已打印 %llu)\n", totalCalls, printed);

	// ---- 4. 抓取结束时刻的调用栈 ----
	printf("\n  ----- Call stack at capture (最内层在最上) -----\n");
	for (int i = sp - 1; i >= 0; i--)
	{
		Symbolize(shadow[i] - 1, s1, sizeof(s1));   // -1 落在 call 指令内部，符号更准

		#if  PRINT_DETAIL
		printf("  #%-3d 0x%016llX  %s\n", sp - 1 - i, shadow[i], s1);
		#endif
	}

	pt_insn_free_decoder(dec);
	pt_image_free(img);
	free(linear);
	free(shadow);
}


// ============================================================
// Save Trace
// ============================================================

static BOOL SaveCurrentTrace(const char* fileName)
{
	DWORD traceSize = 0;

	printf("[+] GetProcessIptTraceSize...\n");

	if (!GetProcessIptTraceSize(
		g_hProcess,
		&traceSize))
	{
		printf(
			"[-] GetProcessIptTraceSize failed: %lu\n",
			GetLastError());

		return FALSE;
	}

	printf(
		"[+] Trace size: %lu bytes\n",
		traceSize);

	if (traceSize == 0)
	{
		printf("[-] Trace size is zero\n");
		return FALSE;
	}


	// --------------------------------------------------------
	// Allocate buffer
	// --------------------------------------------------------

	BYTE* buffer = (BYTE*)VirtualAlloc(
		NULL,
		traceSize,
		MEM_COMMIT | MEM_RESERVE,
		PAGE_READWRITE);

	if (!buffer)
	{
		printf(
			"[-] VirtualAlloc failed: %lu\n",
			GetLastError());

		return FALSE;
	}


	// --------------------------------------------------------
	// Read IPT trace
	// --------------------------------------------------------

	printf("[+] GetProcessIptTrace...\n");

	if (!GetProcessIptTrace(
		g_hProcess,
		buffer,
		traceSize))
	{
		printf(
			"[-] GetProcessIptTrace failed: %lu\n",
			GetLastError());

		VirtualFree(
			buffer,
			0,
			MEM_RELEASE);

		return FALSE;
	}


	// --------------------------------------------------------
	// Create file
	// --------------------------------------------------------

	HANDLE hFile = CreateFileA(
		fileName,
		GENERIC_WRITE,
		0,
		NULL,
		CREATE_ALWAYS,
		FILE_ATTRIBUTE_NORMAL,
		NULL);

	if (hFile == INVALID_HANDLE_VALUE)
	{
		printf(
			"[-] CreateFileA failed: %lu\n",
			GetLastError());

		VirtualFree(
			buffer,
			0,
			MEM_RELEASE);

		return FALSE;
	}


	// --------------------------------------------------------
	// Write file
	// --------------------------------------------------------

	DWORD written = 0;

	BOOL result = WriteFile(
		hFile,
		buffer,
		traceSize,
		&written,
		NULL);

	CloseHandle(hFile);

	// *** PARSE ***
	{
		// --------------------------------------------------------
		// 文件头
		//
		// +0x00 DWORD TraceVersion
		// +0x04 DWORD TraceSize
		// --------------------------------------------------------
		{
			DWORD version =
				*(DWORD*)(buffer + 0x00);

			DWORD traceSize =
				*(DWORD*)(buffer + 0x04);

			printf("File size : %u (0x%X)\n",
				traceSize + 8,
				traceSize + 8);

			printf("Version   : 0x%08X\n",
				version);

			printf("TraceSize : %u (0x%X)\n",
				traceSize,
				traceSize);

			printf("Data start: 0x8\n\n");


			// --------------------------------------------------------
			// IPT_TRACE_HEADER
			//
			// DWORD64 ThreadId            +0x00
			// DWORD   TimingSettings      +0x08
			// DWORD   MtcFrequency        +0x0C
			// DWORD   FrequencyToTscRatio +0x10
			// DWORD   RingBufferOffset    +0x14
			// DWORD   TraceSize           +0x18
			// BYTE    Trace                +0x1C
			// --------------------------------------------------------

			DWORD offset = 8;
			int entry = 0;

			while (offset + 0x1C <= traceSize + 8)
			{
				IPT_TRACE_HEADER* traceHeader =
					(IPT_TRACE_HEADER*)(buffer + offset);

				DWORD64 threadId =
					traceHeader->ThreadId;

				DWORD timingSettings =
					traceHeader->TimingSettings;

				DWORD mtcFrequency =
					traceHeader->MtcFrequency;

				DWORD frequencyToTscRatio =
					traceHeader->FrequencyToTscRatio;

				DWORD ringBufferOffset =
					traceHeader->RingBufferOffset;

				DWORD threadTraceSize =
					traceHeader->TraceSize;


				BYTE* trace =
					traceHeader->Trace;

				DWORD traceStart =
					offset + 0x1C;

				DWORD traceEnd =
					traceStart + threadTraceSize;


				printf("[Trace Entry %d]\n", entry);

				printf("  Header Offset       : 0x%X\n",
					offset);

				printf("  ThreadId            : 0x%llX\n",
					threadId);

				printf("  TimingSettings      : %u\n",
					timingSettings);

				printf("  MtcFrequency        : %u\n",
					mtcFrequency);

				printf("  FrequencyToTscRatio : %u\n",
					frequencyToTscRatio);

				printf("  RingBufferOffset    : %u\n",
					ringBufferOffset);

				printf(
					"  TraceSize           : %u (0x%X)\n",
					threadTraceSize,
					threadTraceSize
				);

				printf(
					"  Trace Offset        : "
					"0x%X - 0x%X\n",
					traceStart,
					traceEnd
				);


				// ----------------------------------------------------
				// 和 Python 一样，直接打印 PT Trace
				// ----------------------------------------------------

				printf("\n");
				printf("  ----- PT Trace -----\n");

				DWORD showSize = threadTraceSize;

				if (showSize > 512)
					showSize = 512;

				printf(
					"  Showing %u / %u bytes\n\n",
					showSize,
					threadTraceSize
				);

				if (0)
				for (DWORD i = 0; i < showSize; i += 16)
				{
					DWORD lineSize = showSize - i;

					if (lineSize > 16)
						lineSize = 16;

					printf("    0x%08X  ",
						traceStart + i);

					for (DWORD j = 0; j < 16; j++)
					{
						if (j < lineSize)
						{
							printf(
								"%02X ",
								trace[i + j]
							);
						}
						else
						{
							printf("   ");
						}
					}

					printf(" ");

					for (DWORD j = 0; j < lineSize; j++)
					{
						BYTE c = trace[i + j];

						if (c >= 0x20 && c <= 0x7E)
							printf("%c", c);
						else
							printf(".");
					}

					printf("\n");
				}

				printf("\n");


				// ----------------------------------------------------
				// 完全按照 Python：
				//
				// offset = trace_end
				// ----------------------------------------------------

				if (traceEnd > traceSize + 8)
				{
					printf("[!] Trace 超出文件范围\n");
					printf(
						"    file size = 0x%X\n",
						traceSize + 8
					);
					printf(
						"    trace end = 0x%X\n",
						traceEnd
					);

					break;
				}

				DWORD64 traceStart64 = (DWORD64)offset + 0x1C;
				DWORD64 traceEnd64 = traceStart64 + threadTraceSize;

				if (traceEnd64 > (DWORD64)traceSize + 8)
				{
					printf("[!] Trace 超出文件范围: end=0x%llX file=0x%X\n", traceEnd64, traceSize + 8);
					break;
				}

				// ... 上面保留你原来的头部字段 printf ...

				printf("\n  ----- Decode -----\n");
				DumpCallStack(trace, threadTraceSize, ringBufferOffset);
				printf("\n");


				offset = traceEnd;
				entry++;
			}

			printf("Total entries: %d\n", entry);
		}
	}


	// --------------------------------------------------------
	// Free buffer
	// --------------------------------------------------------

	VirtualFree(
		buffer,
		0,
		MEM_RELEASE);


	if (!result)
	{
		printf(
			"[-] WriteFile failed: %lu\n",
			GetLastError());

		return FALSE;
	}


	printf(
		"[+] Saved: %s\n",
		fileName);

	printf(
		"[+] Written: %lu bytes\n",
		written);

	sumup();

	return TRUE;
}


BOOL
ConfigureBufferSize(
	_In_ PWCHAR pwszSize,
	_Inout_ PIPT_OPTIONS pOptions
)
{
	DWORD dwSize;
	BOOL bRes;
	bRes = FALSE;

	//
	// Get the buffer size
	//
	dwSize = wcstoul(pwszSize, NULL, 10);
	if (dwSize == 0)
	{
		wprintf(L"[-] Invalid size: %s\n", pwszSize);
		goto Cleanup;
	}

	//
	// Warn the user about incorrect values
	//
	if (!((dwSize) && ((dwSize & (~dwSize + 1)) == dwSize)))
	{
		wprintf(L"[*] Size will be aligned to a power of 2\n");
	}
	else if (dwSize < 4096)
	{
		wprintf(L"[*] Size will be set to minimum of 4KB\n");
	}
	else if (dwSize > (128 * 1024 * 1024))
	{
		wprintf(L"[*] Size will be set to a maximum of 128MB\n");
	}

	//
	// Compute the size option
	//
	pOptions->TopaPagesPow2 = ConvertToPASizeToSizeOption(dwSize);
	bRes = TRUE;
	wprintf(L"[+] Using size: %d bytes\n",
		1 << (pOptions->TopaPagesPow2 + 12));

Cleanup:
	//
	// Return result
	//
	return bRes;
}

BOOL
ConfigureTraceFlags(
	_In_ PWCHAR pwszFlags,
	_Inout_ PIPT_OPTIONS pOptions
)
{
	DWORD dwFlags;
	BOOL bRes;
	bRes = FALSE;

	//
	// Read the flags now and make sure they're valid
	//
	dwFlags = wcstoul(pwszFlags, NULL, 16);
	if (dwFlags & ~IPT_TOOL_VALID_FLAGS)
	{
		wprintf(L"[-] Invalid flags: %s\n", pwszFlags);
		goto Cleanup;
	}

	//
	// If the user didn't specify MTC, but wants CYC, set MTC too as the IPT
	// driver wil enable those packets anyway.
	//
	if ((dwFlags & IPT_TOOL_USE_CYC_TIMING_PACKETS) &&
		!(dwFlags & IPT_TOOL_USE_MTC_TIMING_PACKETS))
	{
		wprintf(L"[*] CYC Packets require MTC packets, adjusting flags!\n");
		dwFlags |= IPT_TOOL_USE_MTC_TIMING_PACKETS;
	}

	//
	// If the user didn't specify MTC, but wants CYC, set MTC too as the IPT
	// driver wil enable those packets anyway.
	//
	if ((dwFlags & (IPT_TOOL_TRACE_KERNEL_MODE | IPT_TOOL_TRACE_ALL_MODE)) ==
		(IPT_TOOL_TRACE_KERNEL_MODE | IPT_TOOL_TRACE_ALL_MODE))
	{
		wprintf(L"[-] Cannot enable both `kernel` and `user + kernel` tracing."
			L" Please pick a single flag to use!\n");
		goto Cleanup;
	}

	//
	// There are no matching options for process tradces
	//
	pOptions->MatchSettings = IptMatchByAnyApp;

	//
	// Choose the right timing setting
	//
	if (dwFlags & IPT_TOOL_USE_MTC_TIMING_PACKETS)
	{
		pOptions->TimingSettings = IptEnableMtcPackets;
		pOptions->MtcFrequency = 3; // FIXME
	}
	else if (dwFlags & IPT_TOOL_USE_CYC_TIMING_PACKETS)
	{
		pOptions->TimingSettings = IptEnableCycPackets;
		pOptions->CycThreshold = 1; // FIXME
	}
	else
	{
		pOptions->TimingSettings = IptNoTimingPackets;
	}

	//
	// Choose the right mode setting
	//
	if (dwFlags & IPT_TOOL_TRACE_KERNEL_MODE)
	{
		pOptions->ModeSettings = IptCtlKernelModeOnly;
	}
	else if (dwFlags & IPT_TOOL_TRACE_ALL_MODE)
	{
		pOptions->ModeSettings = IptCtlUserAndKernelMode;
	}
	else
	{
		pOptions->ModeSettings = IptCtlUserModeOnly;
	}

	//
	// Print out chosen options
	//
	bRes = TRUE;
	wprintf(L"[+] Tracing Options:\n"
		L"           Match by: %s\n"
		L"         Trace mode: %s\n"
		L"     Timing packets: %s\n",
		L"Any process",
		(pOptions->ModeSettings == IptCtlUserAndKernelMode) ?
		L"Kernel and user-mode" :
		(pOptions->ModeSettings == IptCtlKernelModeOnly) ?
		L"Kernel-mode only" : L"User-mode only",
		(pOptions->TimingSettings == IptEnableMtcPackets) ?
		L"MTC Packets" :
		(pOptions->TimingSettings == IptEnableCycPackets) ?
		L"CYC Packets" : L"No  Packets");

Cleanup:
	//
	// Return result
	//
	return bRes;
}
FORCEINLINE
DWORD
ConvertToPASizeToSizeOption(
	_In_ DWORD dwSize
)
{
	DWORD dwIndex;

	//
	// Cap the size to 128MB. Sizes below 4KB will result in 0 anyway.
	//
	if (dwSize > (128 * 1024 * 1024))
	{
		dwSize = 128 * 1024 * 1024;
	}

	//
	// Find the nearest power of two that's set (align down)
	//
	BitScanReverse(&dwIndex, dwSize);

	//
	// The value starts at 4KB
	//
	dwIndex -= 12;
	return dwIndex;
}
// ============================================================
// Start IPT
// ============================================================

static BOOL StartTrace()
{
	clean();
	printf("[+] Starting IPT...\n");

	IPT_OPTIONS options;
	options.OptionVersion = 1;
	ConfigureBufferSize(L"32768", &options);
	//ConfigureBufferSize(L"67108864", &options);
	ConfigureTraceFlags(L"0", &options);
	if (!StartProcessIptTracing(
		g_hProcess,
		options))
	{
		printf(
			"[-] StartProcessIptTracing failed: %lu\n",
			GetLastError());

		return FALSE;
	}

	printf("[+] IPT START\n");

	return TRUE;
}


// ============================================================
// Capture IPT
// ============================================================

static BOOL CaptureTrace()
{
	printf("[+] Capturing IPT...\n");


	// --------------------------------------------------------
	// 先读取 Trace
	//
	// 这和你之前：
	//
	// ipttool --trace 0x4C44 trace.dat
	//
	// 的行为一致。
	// --------------------------------------------------------

	BOOL result = SaveCurrentTrace("C:\\Users\\Administrator\\Desktop\\123.bin)");

	// --------------------------------------------------------
	// 再停止 IPT
	// --------------------------------------------------------

	printf("[+] Stopping IPT...\n");

	if (!StopProcessIptTracing(
		g_hProcess))
	{
		printf(
			"[-] StopProcessIptTracing failed: %lu\n",
			GetLastError());
	}
	else
	{
		printf("[+] IPT STOP\n");
	}


	return result;
}


// ============================================================
// Worker Thread
// ============================================================

static DWORD WINAPI TraceThread(
	LPVOID parameter)
{
	UNREFERENCED_PARAMETER(parameter);


	printf("\n");
	printf("========================================\n");
	printf(" IPT DLL TID: %X\n", GetCurrentThreadId());
	printf("========================================\n");
	printf("\n");

	printf("[+] Current process handle: %p\n",
		g_hProcess);

	printf("[+] Press ENTER to START IPT\n");


	BOOL lastDown = FALSE;


	while (InterlockedCompareExchange(
		&g_running,
		0,
		0))
	{
		SHORT state = GetAsyncKeyState(
			VK_RETURN);

		BOOL down =
			(state & 0x8000) != 0;


		// ----------------------------------------------------
		// ENTER 上升沿
		// ----------------------------------------------------

		if (down && !lastDown)
		{
			// =================================================
			// 第一次 ENTER
			// =================================================

			if (!g_tracing)
			{
				printf("\n");
				printf("[+] ENTER -> START\n");

				if (StartTrace())
				{
					g_tracing = TRUE;

					printf(
						"[+] Recording IPT...\n");

					printf(
						"[+] Do whatever you want now.\n");

					printf(
						"[+] Press ENTER again to capture.\n");
				}
			}

			// =================================================
			// 第二次 ENTER
			// =================================================

			else
			{
				printf("\n");
				printf("[+] ENTER -> CAPTURE\n");

				CaptureTrace();

				g_tracing = FALSE;

				printf("\n");
				printf(
					"[+] Trace finished.\n");

				printf(
					"[+] Saved to C:\\Temp\\123.bin\n");

				printf(
					"[+] Press ENTER to start again.\n");
			}
		}


		// 保存上一帧 Enter 状态
		lastDown = down;


		// 防止占满 CPU
		Sleep(1);
	}


	return 0;
}


// ============================================================
// DllMain
// ============================================================

BOOL WINAPI DllMain(
	HMODULE hModule,
	DWORD reason,
	LPVOID reserved)
{
	UNREFERENCED_PARAMETER(reserved);


	switch (reason)
	{
	case DLL_PROCESS_ATTACH:
	{
		DisableThreadLibraryCalls(
			hModule);

		AllocConsole();	
		SetConsoleCP(65001); SetConsoleOutputCP(65001);
		SetConsoleMode(GetStdHandle(STD_OUTPUT_HANDLE), 7);

		FILE* fp = 0;

		freopen_s(&fp, "CONOUT$", "w", stdout);
		freopen_s(&fp, "CONOUT$", "w", stderr);

		if (0) {
			freopen_s(&fp, logpath, "w", stdout);
			freopen_s(&fp, logpath, "w", stderr);
			setvbuf(stdout, 0, _IONBF, 0);
			setvbuf(stderr, 0, _IONBF, 0);
		}

		freopen_s(&fp, "CONIN$", "r", stdin);

		PBYTE a = (PBYTE)GetModuleHandleW(NULL);

		g_end = a +
			((PIMAGE_NT_HEADERS)(a + ((PIMAGE_DOS_HEADER)a)->e_lfanew))
			->OptionalHeader.SizeOfImage;

		HANDLE hThread = CreateThread(
			NULL,
			0,
			TraceThread,
			NULL,
			0,
			NULL);


		if (hThread)
		{
			CloseHandle(hThread);
		}

		break;
	}


	case DLL_PROCESS_DETACH:
	{
		InterlockedExchange(
			&g_running,
			0);

		break;
	}
	}


	return TRUE;
}