#include <cstdint>

// A read through a pointer that may be null does not prove, in code and in a contract, decision 0140.
int32_t read(const int32_t* p) {
  return *p;
}

//@ ensures result == *p
int32_t same(const int32_t* p) {
  return 0;
}

//@ requires p != nullptr
int32_t needs(const int32_t* p) {
  return *p;
}

int32_t caller() {
  return needs(nullptr);
}
