#include <array>
#include <bit>
#include <cstdint>
#include <memory>
#include <vector>
#include "../../../../include/cplusp.h"

struct CPLUSP_PLAIN("an old record") Record {
  int count = 0;
  int extra = 0;
  // A verified member of a plain type keeps its declaration in view, decision 0052.
  CPLUSP_VERIFIED
  std::shared_ptr<int32_t> share() const {
    return {};
  }
};

// A binding by reference reads the fields.
int32_t bound(const Record& r) {
  const auto& [c, e] = r; return c + e;
}

// The library reads a plain object that verified code hands it.
int32_t bytes(const Record& r) {
  return std::bit_cast<std::array<int32_t, 2>>(r)[1];
}

// A library type that holds a plain type is a use of it.
int32_t held() {
  std::vector<Record> v;
  return 0;
}

// A member of a plain type that overrides a function that is not plain is plain, and it is refused where it overrides.
struct Shape {
  virtual ~Shape() = default;
  //@ ensures true
  virtual int32_t area() const = 0;
};

struct CPLUSP_PLAIN("an old shape") Legacy : Shape {
  CPLUSP_TRUSTED("releases the old shape")
  //@ ensures true
  ~Legacy() override;
  int32_t area() const override;
};
