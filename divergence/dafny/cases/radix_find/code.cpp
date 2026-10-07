#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <vector>

// A radix tree over byte keys, the shape of the find in mattyv/FlashRadixTree. The prefix is the bytes on the edge into a node, and a
// node holds a value when a key ends there. Wellformed says that no child has an empty prefix and that no two children of a node start
// with the same byte. Stored says that the tree maps the key to the value. Height is the length of the longest path. The model defines
// all three over the tree.
struct Node {
  std::vector<uint8_t> prefix;
  std::optional<int32_t> value;
  std::vector<Node> children;
};

// The value under the key, where the key starts below the node's own prefix. The tree holds at most one value for a key, so the
// result is that value, or none when the tree holds the key with no value. The height bound is the rule of the case stack_depth. The
// prefix must fit the key before subspan takes the rest.
//@ requires Wellformed(n) && Height(n) <= 1000
//@ decreases Height(n)
//@ ensures forall v :: result == Some(v) <==> Stored(n, key, v)
std::optional<int32_t> find(const Node& n, std::span<const uint8_t> key) {
  if (key.empty()) {
    return n.value;
  }
  for (std::size_t i = 0; i < n.children.size(); ++i) {
    if (n.children[i].prefix[0] == key[0]) {
      if (n.children[i].prefix.size() > key.size()) {
        return std::nullopt;
      }
      for (std::size_t j = 0; j < n.children[i].prefix.size(); ++j) {
        if (n.children[i].prefix[j] != key[j]) {
          return std::nullopt;
        }
      }
      return find(n.children[i], key.subspan(n.children[i].prefix.size()));
    }
  }
  return std::nullopt;
}
