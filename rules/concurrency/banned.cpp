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
  auto f = std::async(std::launch::deferred, square, x);  // BANNED also: global_state
  return f.get();
}

void via_thread(int32_t x) {
  std::thread t(square, x);  // BANNED
  t.join();
}

void store_through_ref(int32_t& x) {
  std::atomic_ref<int32_t> a{x};  // BANNED
  a.store(1);
}

#include <algorithm>
#include <condition_variable>
#include <execution>
#include <shared_mutex>

void wait_any(std::condition_variable_any& cv);  // BANNED
void lock_shared_timed(std::shared_timed_mutex& m);  // BANNED
void lock_recursive_timed(std::recursive_timed_mutex& m);  // BANNED

void sort_parallel(std::vector<int32_t>& v) {
  std::sort(std::execution::par, v.begin(), v.end());  // BANNED
}
