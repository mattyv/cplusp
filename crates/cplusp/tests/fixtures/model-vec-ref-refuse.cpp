#include <cstddef>
#include <cstdint>
#include <vector>

// A vector by reference that the modifies line does not name, push_back, a compound write, a vector of bool, and a call that
// passes the vector on to a writer, have no rule, decisions 0145 and 0147.
void unnamed(std::vector<int32_t>& v) {
}

//@ modifies v
void append(std::vector<int32_t>& v, int32_t x) {
  v.push_back(x);
}

//@ requires 0 < v.size()
//@ modifies v
void add(std::vector<int32_t>& v) {
  v[0] += 1;
}

//@ modifies v
void flags(std::vector<bool>& v) {
}

//@ requires 0 < w.size()
//@ modifies w
void set7(std::vector<int32_t>& w) {
  w[0] = 7;
}

//@ requires 0 < v.size()
//@ modifies v
void pass_on(std::vector<int32_t>& v) {
  set7(v);
}
