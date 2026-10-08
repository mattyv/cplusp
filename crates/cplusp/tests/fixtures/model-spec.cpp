#include <cstddef>
#include <cstdint>
#include <vector>

// Specification functions come from the companion file model-spec.spec.dfy, decision 0079.
struct Node {
  std::vector<uint8_t> prefix;
  std::vector<Node> children;
};

//@ ensures result == Max(a, b)
//@ ensures Above(result)
int32_t larger(int32_t a, int32_t b) {
  if (a < b) {
    return b;
  }
  return a;
}

//@ ensures result == Leaf(n)
bool leaf(const Node& n) {
  return n.children.empty();
}

//@ requires Wellformed(n) && !n.children.empty()
//@ ensures result > 0
size_t first_edge(const Node& n) {
  return n.children[0].prefix.size();
}
