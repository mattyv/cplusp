#include <cstdint>

struct Readable {
  virtual int32_t read() const = 0;
  virtual ~Readable() = default;
};

struct Countable {
  virtual int32_t count() const = 0;
  virtual ~Countable() = default;
};

struct Store : Readable, Countable {
  int32_t value = 0;
  int32_t items = 0;
  int32_t read() const override { return value; }
  int32_t count() const override { return items; }
};

//@ requires 0 <= s.value <= 1000 && 0 <= s.items <= 1000
//@ ensures result == s.value + s.items
int32_t both(const Store& s) {
  const Readable& r = s;
  const Countable& c = s;
  return r.read() + c.count();
}
