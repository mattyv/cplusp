// The edge where the model and the C++ agree: the key 01 in the tree of the driver. Two stored keys, 010 and 011, pass through the
// node 01, and that node holds no value. So the find gives none. The find of FlashRadixTree gives the value of 01001 for the same
// shape, because its loop goes on below a node where the key ends. The model says none.
#include <cstdint>
#include <cstdio>
#include <optional>
#include <span>
#include <vector>

struct Node {
  std::vector<uint8_t> prefix;
  std::optional<int32_t> value;
  std::vector<Node> children;
};

std::optional<int32_t> find(const Node& n, std::span<const uint8_t> key);

int main() {
  Node tree{{}, std::nullopt, {
    Node{{0, 1}, std::nullopt, {
      Node{{0}, 1, {Node{{0, 1}, 2, {}}}},
      Node{{1}, 3, {}},
    }},
    Node{{1}, 4, {}},
    Node{{2, 2}, 5, {}},
  }};
  std::vector<uint8_t> key = {0, 1};
  std::optional<int32_t> r = find(tree, key);
  if (r.has_value()) {
    std::printf("%d\n", *r);
  } else {
    std::printf("none\n");
  }
  return 0;
}
