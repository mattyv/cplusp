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

//@ ensures result == r.read()
int32_t read_of(const Readable& r) {
  return r.read();
}

//@ ensures result == c.count()
int32_t count_of(const Countable& c) {
  return c.count();
}

//@ requires 0 <= s.value <= 1000 && 0 <= s.items <= 1000
//@ ensures result == s.value + s.items
int32_t both(const Store& s) {
  return read_of(s) + count_of(s);
}
