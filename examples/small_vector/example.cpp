#include <array>
#include <cstddef>
#include <cstdint>

// A vector of at most eight elements, with no allocation: eight slots in a std::array and a count of the ones in use. The capacity is
// the constant 8, and not a template parameter. The usual form is `template <size_t N> class SmallVector`, and the gate refuses it:
// "Function and class templates: outside its limit. Limit: Type parameters only, no specialisation. Use a template with type
// parameters only." A non-type parameter makes each N a type of its own, and the prover has no model for a number in a type. So a
// vector of another capacity is another class, written out. A push on a full vector changes nothing and says so in its result.
// The contracts use the implicit this, decision 0028, and valid() is the invariant. A contract reads `v.size()` as the size of a
// vector, so the count is length(), decision 0191.
// ponytail: the capacity is 8 for every vector. The upgrade is one more class for each other capacity.
class SmallVector {
 public:
  //@ ensures valid() && length() == 0
  SmallVector() : items_(), count_(0) {}

  //@ ensures result == (count_ <= 8)
  bool valid() const { return count_ <= 8; }

  //@ requires valid()
  //@ ensures result == count_
  size_t length() const { return count_; }

  //@ requires valid() && i < length()
  //@ ensures result == items_[i]
  int32_t at(size_t i) const { return items_[i]; }

  //@ requires valid()
  //@ ensures valid() && result == (old(length()) < 8)
  //@ ensures length() == (result ? old(length()) + 1 : old(length()))
  //@ ensures result ==> at(length() - 1) == x
  //@ ensures forall i :: 0 <= i < old(length()) ==> at(i) == old(at(i))
  bool push(int32_t x) {
    if (count_ == 8) {
      return false;
    }
    items_[count_] = x;
    count_ += 1;
    return true;
  }

 private:
  std::array<int32_t, 8> items_;
  size_t count_;
};

// A verified caller. Eight pushes are accepted and the ninth is refused.
//@ ensures result == false
bool ninth_push_is_refused() {
  SmallVector v;
  //@ invariant 0 <= i <= 8 && v.valid() && v.length() == i
  for (int32_t i = 0; i < 8; ++i) {
    v.push(i);
  }
  return v.push(8);
}

//@ ensures result == 7
int32_t sum_of_two() {
  SmallVector v;
  v.push(3);
  v.push(4);
  return v.at(0) + v.at(1);
}
