#include <cstdint>

struct Money {
  int32_t cents;
};

//@ requires 0 <= a.cents <= 1000 && 0 <= b.cents <= 1000
//@ ensures result.cents == (a.cents + b.cents > 1000 ? 1000 : a.cents + b.cents)
Money operator+(Money a, Money b) {
  if (a.cents + b.cents > 1000) {
    return Money{1000};
  }
  return Money{a.cents + b.cents};
}

//@ requires 0 <= a.cents <= 1000 && 0 <= b.cents <= 1000
//@ ensures result.cents == (a.cents + b.cents > 1000 ? 1000 : a.cents + b.cents)
Money total(Money a, Money b) {
  return a + b;
}
