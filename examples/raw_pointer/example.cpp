#include <cstdint>

// A raw pointer is a non-owning parameter that names one object. Whether it may be null is in the contract. There is no
// pointer arithmetic, no pointer member and no pointer local, so the pointer cannot outlive its object.
//@ requires p != nullptr
//@ ensures result == *p
int32_t read(const int32_t* p) {
  return *p;
}

//@ ensures result == (p == nullptr ? fallback : *p)
int32_t read_or(const int32_t* p, int32_t fallback) {
  if (p == nullptr) {
    return fallback;
  }
  return *p;
}
