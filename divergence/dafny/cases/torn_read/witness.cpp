// The edge where the naive model and the C++ part ways: another thread writes `shared` while difference() reads it twice.
// The two reads can see two values, so difference() is not 0. The writes are a data race, and ThreadSanitizer reports them.
// ThreadSanitizer can miss a race in a busy loop on a loaded machine, so the first part is one write and one read.
// The second part is a writer in a loop. The loop stops at the first call that is not 0, and the program prints 1.
#include <atomic>
#include <cstdint>
#include <cstdio>
#include <thread>

extern int32_t shared;
int32_t difference();

int main() {
  std::atomic<bool> written{false};
  std::thread once([&written] {
    shared = 1;
    written.store(true, std::memory_order_relaxed);
  });
  while (!written.load(std::memory_order_relaxed)) {
  }
  difference();
  once.join();

  std::atomic<bool> done{false};
  std::thread writer([&done] {
    for (int32_t i = 0; !done; i = (i + 1) % 1000) {
      shared = i;
    }
  });
  bool torn = false;
  for (int calls = 0; calls < 10000000 && !torn; ++calls) {
    torn = difference() != 0;
  }
  done = true;
  writer.join();
  std::printf("%d\n", torn);
  return 0;
}
