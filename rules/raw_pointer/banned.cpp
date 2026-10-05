#include <cstdint>

struct Holder {
  const int32_t* p = nullptr;  // BANNED
};

int32_t read_later(int32_t x) {
  const int32_t* q = &x;  // BANNED
  return *q;
}

#include <vector>

struct Watcher {
  virtual ~Watcher() = default;
  virtual void on_change(int32_t v) = 0;
};

struct Subject {
  std::vector<Watcher*> watchers;  // BANNED
};
