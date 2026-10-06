#include <unordered_set>
#include <unordered_map>

extern "C" {
	void Symbolize(uint64_t addr, char* out, size_t cap);
}

static std::unordered_set<uintptr_t> okk;
static std::unordered_map<uintptr_t, unsigned> map;

extern "C" void clean() {
	map.clear();
}

extern "C" void enter(uintptr_t _to) {
	map[_to]++;
}
extern "C" void sumup() {
	printf("\n\n\n");

	if (!okk.empty()) {
		std::unordered_set<uintptr_t> ok;
		for (auto it = map.begin(); it != map.end(); ++it) {
			if (it->second == 1) {
				ok.insert(it->first);
			}
		}

		// È¡½»¼¯ ok ^ okk 
		for (auto it = okk.begin(); it != okk.end(); ) {

			if (ok.find(*it) == ok.end()) {
				it = okk.erase(it);
			}
			else {
				++it;
			}
		}

		for (auto it = okk.begin(); it != okk.end(); ++it) {
			char buf[256];

			Symbolize(*it, buf, sizeof(buf));
			printf("* %s: %u\n", buf, map[*it]);

		}

		okk.clear();
		return;
	}

	for (auto it = map.begin(); it != map.end(); ++it) {
		char buf[256];
		if (it->second == 1) {
			Symbolize(it->first, buf, sizeof(buf));
			printf("%s: %u\n", buf, it->second);

			okk.insert(it->first);
		}
	}


}