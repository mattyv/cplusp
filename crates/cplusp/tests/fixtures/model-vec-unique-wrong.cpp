#include <cstdint>
#include <memory>
#include <vector>

// An element that may be null, an index that may be out of range, and a read of an element before its write, decision 0170.
struct Shape {
  virtual ~Shape() = default;
  virtual bool valid() const = 0;
  //@ requires valid()
  //@ ensures 0 <= result && result <= 1000000
  virtual int32_t area() const = 0;
};

//@ requires v.size() == 1 && (v[0] != nullptr ==> v[0]->valid())
int32_t first_null(const std::vector<std::unique_ptr<Shape>>& v) {
  return v[0]->area();
}

//@ requires forall i :: 0 <= i < v.size() ==> v[i] != nullptr && v[i]->valid()
int32_t first_range(const std::vector<std::unique_ptr<Shape>>& v) {
  return v[0]->area();
}

struct Observer {
  virtual ~Observer() = default;
  virtual bool valid() const = 0;
  //@ requires valid()
  //@ ensures 0 <= result && result <= 1000
  virtual int32_t seen() const = 0;
  //@ requires valid() && seen() < 1000
  //@ ensures valid() && seen() == old(seen()) + 1
  virtual void on_change(int32_t v) = 0;
};

//@ modifies v
//@ requires v.size() == 1 && v[0] != nullptr && v[0]->valid() && v[0]->seen() == 0
void once(std::vector<std::unique_ptr<Observer>>& v) {
  v[0]->on_change(1);
  //@ assert v[0]->seen() == 0
  v[0]->on_change(2);
}
