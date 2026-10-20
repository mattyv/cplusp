#include <cstdint>

// Two interfaces of one name, decision 0166.
namespace a {
struct Shape {
  virtual ~Shape() = default;
  //@ ensures 3 <= result && result <= 1000
  virtual int32_t corners() const = 0;
};
}  // namespace a

namespace b {
struct Shape {
  virtual ~Shape() = default;
  //@ ensures 0 <= result && result <= 1000
  virtual int32_t corners() const = 0;
};
}  // namespace b

//@ ensures result >= 3
int32_t both(const a::Shape& p, const b::Shape& q) {
  return p.corners() + q.corners();
}
