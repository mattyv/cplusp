#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

// A class that a loop can walk. The classic form has begin() and end() so that a range-for takes it:
// `std::vector<int32_t>::const_iterator begin() const { return items_.begin(); }`, and the same for end(). The range-for that uses it
// is no finding. The gate refuses begin() and end() at their lines, because the iterator leaves the call that made it: "Iterators:
// outside its limit. Limit: Range-for only. The loop body does not change the range, by a call on it or through a function. begin and
// end may appear only as direct arguments of a std:: call. No stored iterator, no std::next, prev, advance or distance. Use a
// range-for loop, or an index the prover can check." The two other ways to write them are refused as well. Pointers, as in
// `items_.data()` and `items_.data() + items_.size()`, are refused under the row for containers, which bans a pointer into a
// container, and under the row for pointer arithmetic. An iterator class of its own is refused under the row for operator
// overloading at its `operator++`, and under the row for lvalue references at the reference member that it keeps.
// So the class gives out the size and the element at an index, and the code that walks it counts. Each call is checked against
// the size by the prover.
class Series {
 public:
  //@ ensures length() == items.size() && forall i :: 0 <= i < length() ==> at(i) == items[i]
  explicit Series(std::vector<int32_t> items) : items_(std::move(items)) {}

  // A contract reads `s.size()` as the size of a vector, so the member function has another name, decision 0191.
  //@ ensures result == items_.size()
  size_t length() const { return items_.size(); }

  //@ requires i < length()
  //@ ensures result == items_[i]
  int32_t at(size_t i) const { return items_.at(i); }

 private:
  std::vector<int32_t> items_;
};

// The walk. The contract says that the result is an element and that no element is larger.
//@ requires s.length() > 0
//@ ensures exists i :: 0 <= i < s.length() && s.at(i) == result
//@ ensures forall i :: 0 <= i < s.length() ==> s.at(i) <= result
int32_t largest(const Series& s) {
  int32_t m = s.at(0);
  //@ invariant 1 <= i <= s.length()
  //@ invariant exists j :: 0 <= j < i && s.at(j) == m
  //@ invariant forall j :: 0 <= j < i ==> s.at(j) <= m
  for (size_t i = 1; i < s.length(); ++i) {
    if (s.at(i) > m) {
      m = s.at(i);
    }
  }
  return m;
}

//@ ensures result == 9
int32_t demo() {
  std::vector<int32_t> items;
  items.push_back(3);
  items.push_back(9);
  items.push_back(4);
  const Series s(std::move(items));
  return largest(s);
}
