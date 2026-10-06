#include <cstdint>

int32_t total = 0;

struct Base {
  virtual ~Base() = default;
  //@ requires total < 0x7FFFFFFF
  //@ modifies total
  virtual void act() {
    total += 1;
  }
};

#include "twice-step.h"
#define SECOND
#include "twice-step.h"
