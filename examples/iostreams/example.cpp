#include <cstdint>
#include "../../include/cplusp.h"

// The trial on a real file found that most of its gate findings were lines that print to std::cout. A stream is a global the
// whole program shares, and output is a side effect no contract describes, so the gate refuses a stream in verified code at its
// line under the row `iostreams`: "`std::cout`, `std::cerr`, streams: allowed only in trusted code. A stream is a global the whole
// program shares, and output is a side effect no contract describes. The model has no I/O. Use return the value, and print it in a
// trusted function with a reason." The shape that passes: verified code computes the value and proves it, and one trusted
// function prints it. Its body is in trusted.cpp.
//@ requires 0 < whole && 0 <= part && part <= whole
//@ ensures 0 <= result && result <= 100
int32_t percent(int32_t part, int32_t whole) {
  return static_cast<int32_t>((static_cast<int64_t>(part) * 100) / whole);
}

CPLUSP_TRUSTED("writes the number and a percent sign to std::cout")
//@ requires 0 <= p && p <= 100
void print_percent(int32_t p);

// A verified caller: the proof is about the number, and the print is a trusted call with a precondition the proof discharges.
//@ requires 0 < whole && 0 <= part && part <= whole
void report(int32_t part, int32_t whole) {
  print_percent(percent(part, whole));
}
