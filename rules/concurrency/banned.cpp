#include <atomic>
#include <future>
#include <mutex>
#include <thread>
#include <vector>

int square(int x) {
  return x * x;
}

int via_mutex(int x) {
  std::mutex m;  // BANNED
  std::lock_guard<std::mutex> lock(m);  // BANNED
  return square(x);
}

int via_atomic(int x) {
  std::atomic<int> a{x};  // BANNED
  return a.load();
}

int load_shared(std::atomic<int>& a) {  // BANNED
  return std::atomic_load(&a);  // BANNED
}

int load_pointer(const std::atomic<int>* a) {  // BANNED
  return a->load();
}

void unlock_shared(std::mutex& m) {  // BANNED
  m.unlock();
}

int count_threads(const std::vector<std::thread>& threads) {  // BANNED
  return threads.empty() ? 0 : 1;
}

int via_async(int x) {
  auto f = std::async(std::launch::deferred, square, x);  // BANNED
  return f.get();
}

void via_thread(int x) {
  std::thread t(square, x);  // BANNED
  t.join();
}
