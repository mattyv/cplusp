// The edge where the naive model and the C++ part ways: 600 and 600 go through operator+, which saturates at 1000.
#include <cstdint>
#include <cstdio>

struct Money {
  int32_t cents;
};

Money total(Money a, Money b);

int main() {
  std::printf("%d\n", total(Money{600}, Money{600}).cents);
  return 0;
}
