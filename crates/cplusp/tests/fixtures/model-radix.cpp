#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <vector>

// The thin slice: the battery case radix_find, decisions 0056 and 0072. The prefix is the bytes on the edge into a node, and a
// node holds a value when a key ends there. Wellformed, Stored and Height are in model-radix.spec.dfy. The height bound is the rule
// of the case stack_depth. A recursion into a child decreases the node.
struct Node {
  std::vector<uint8_t> prefix;
  std::optional<int32_t> value;
  std::vector<Node> children;
};

//@ requires Wellformed(n) && Height(n) <= 1000
//@ decreases n
//@ ensures forall v :: result.has_value() && result.value() == v ==> Stored(n, key, v)
//@ ensures forall v :: Stored(n, key, v) ==> result.has_value() && result.value() == v
std::optional<int32_t> find(const Node& n, std::span<const uint8_t> key) {
  if (key.empty()) {
    return n.value;
  }
  //@ invariant i <= n.children.size()
  //@ invariant forall k :: 0 <= k < i ==> n.children[k].prefix[0] != key[0]
  //@ decreases n.children.size() - i
  for (size_t i = 0; i < n.children.size(); ++i) {
    if (n.children[i].prefix[0] == key[0]) {
      if (n.children[i].prefix.size() > key.size()) {
        return std::nullopt;
      }
      //@ invariant j <= n.children[i].prefix.size()
      //@ invariant forall m :: 0 <= m < j ==> n.children[i].prefix[m] == key[m]
      //@ decreases n.children[i].prefix.size() - j
      for (size_t j = 0; j < n.children[i].prefix.size(); ++j) {
        if (n.children[i].prefix[j] != key[j]) {
          return std::nullopt;
        }
      }
      return find(n.children[i], key.subspan(n.children[i].prefix.size()));
    }
  }
  return std::nullopt;
}
