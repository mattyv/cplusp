// The edge where the model and the C++ agree: both calls go to the functions of Store, whichever interface names them.
// The classes are the same text as in code.cpp, so the definitions agree. Prints the sum for 3 and 4.
#include <cstdint>
#include <cstdio>

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

int32_t both(const Store& s);

int main() {
  Store s;
  s.value = 3;
  s.items = 4;
  std::printf("%d\n", both(s));
  return 0;
}
