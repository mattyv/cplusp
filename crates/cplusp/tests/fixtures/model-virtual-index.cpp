#include <cstdint>
#include <vector>

// A requires line of an interface that may read out of range fails once, at that line, decision 0165.
class Shape {
 public:
  virtual ~Shape() = default;
  //@ requires v[0] > 0
  virtual int32_t first(const std::vector<int32_t>& v) const = 0;
};

class Square final : public Shape {
 public:
  //@ requires v.size() > 0
  int32_t first(const std::vector<int32_t>& v) const override { return v[0]; }
};
