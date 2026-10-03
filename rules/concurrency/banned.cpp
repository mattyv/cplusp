#include <cstdint>
#include <atomic>
#include <future>
#include <mutex>
#include <thread>
#include <vector>

int32_t square(int32_t x) {
  return x * x;
}

int32_t via_mutex(int32_t x) {
  std::mutex m;  // BANNED
  std::lock_guard<std::mutex> lock(m);  // BANNED
  return square(x);
}

int32_t via_atomic(int32_t x) {
  std::atomic<int32_t> a{x};  // BANNED
  return a.load();
}

int32_t load_shared(std::atomic<int32_t>& a) {  // BANNED
  return std::atomic_load(&a);  // BANNED
}

int32_t load_pointer(const std::atomic<int32_t>* a) {  // BANNED
  return a->load();
}

void unlock_shared(std::mutex& m) {  // BANNED
  m.unlock();
}

int32_t count_threads(const std::vector<std::thread>& threads) {  // BANNED
  return threads.empty() ? 0 : 1;
}

int32_t via_async(int32_t x) {
  auto f = std::async(std::launch::deferred, square, x);  // BANNED
  return f.get();
}

void via_thread(int32_t x) {
  std::thread t(square, x);  // BANNED
  t.join();
}
