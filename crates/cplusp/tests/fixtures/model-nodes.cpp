#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <vector>

// Structs that hold sequences, and recursive structs, decision 0076.
struct Node {
  std::vector<uint8_t> prefix;
  std::optional<int32_t> value;
  std::vector<Node> children;
};

//@ requires n.prefix.size() > 0
//@ ensures result == n.prefix[0]
uint8_t first(const Node& n) {
  return n.prefix[0];
}

//@ requires i < n.children.size() && n.children[i].prefix.size() > 0
//@ ensures result == n.children[i].prefix[0]
uint8_t child_first(const Node& n, size_t i) {
  return n.children[i].prefix[0];
}

//@ decreases n
//@ ensures n.children.size() == 0 ==> result == n.value
std::optional<int32_t> leftmost(const Node& n) {
  if (n.children.size() == 0) {
    return n.value;
  }
  return leftmost(n.children[0]);
}

//@ ensures result ==> forall j :: 0 <= j < n.children.size() ==> n.children[j].prefix.size() > 0
bool edges(const Node& n) {
  //@ invariant i <= n.children.size()
  //@ invariant forall j :: 0 <= j < i ==> n.children[j].prefix.size() > 0
  //@ decreases n.children.size() - i
  for (size_t i = 0; i < n.children.size(); ++i) {
    if (n.children[i].prefix.size() == 0) {
      return false;
    }
  }
  return true;
}

struct Point {
  int32_t x;
  int32_t y;
};

//@ requires v.size() > 0
//@ ensures result == v[0].x
int32_t first_x(std::span<const Point> v) {
  return v[0].x;
}
