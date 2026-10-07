// The differential driver: the same fixed tree as drive.dfy, and the find of each generated key, as a decimal or `none`.
#include <cstdint>
#include <cstdio>
#include <optional>
#include <span>
#include <vector>

#include "inputs.h"

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
  for (std::size_t i = 0; i < runs; ++i) {
    std::optional<int32_t> r = find(tree, arg0[i]);
    if (r.has_value()) {
      std::printf("%d\n", *r);
    } else {
      std::printf("none\n");
    }
  }
  return 0;
}
