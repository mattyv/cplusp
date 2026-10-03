#include <cstdint>

struct Base {
  int32_t seen = 0;
  Base() { seen = kind(); }  // BANNED
  virtual int32_t kind() const { return 1; }
  virtual ~Base() = default;
};

struct Logger {
  virtual void log() const {}
  virtual ~Logger() { log(); }  // BANNED
};
