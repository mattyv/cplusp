// The edge where the naive model and the C++ part ways: base_value and derived are in different files.
// The standard does not say which file initializes first. The harness links code.cpp first, so derived is set
// while base_value is still 0, and read_derived() returns 1. With fixed.cpp the value is computed on demand, and it is 6.
#include <cstdint>
#include <cstdio>

int32_t read_derived();

int32_t five() {
  return 5;
}

int32_t base_value = five();

int main() {
  std::printf("%d\n", read_derived());
  return 0;
}
