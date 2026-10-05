#include <cstdint>
#include <memory>
#include <utility>

// A binary tree whose nodes own their children through unique_ptr. A null pointer is an empty tree. Size, Sum and Within are the
// specification functions, and example.dfy defines them over the tree: the number of nodes, the sum of the values, and the test that
// every value is at most a bound in magnitude. The recursion needs a decreases clause, and the size of the tree is the measure,
// because each child is smaller than its parent. The stack is finite, so the contract bounds the size, and that bounds the depth.
// The bound on the values and the bound on the size together keep every partial sum inside int32_t. A const handle gives const
// access through it, decision 0030, and sum only reads, so it takes the tree by const reference.
// ponytail: the bound is on the size of the tree, which bounds the depth. A degenerate tree of 1000 nodes is 1000 calls deep. The upgrade
// is a bound on the depth, and a bound on the size that follows from it.
struct Node {
  int32_t value = 0;
  std::unique_ptr<Node> left;
  std::unique_ptr<Node> right;
};

//@ requires Size(root) <= 1000 && Within(root, 1000000)
//@ decreases Size(root)
//@ ensures result == Sum(root)
int32_t sum(const std::unique_ptr<Node>& root) {
  if (root == nullptr) {
    return 0;
  }
  int32_t from_left = sum(root->left);
  int32_t from_right = sum(root->right);
  return root->value + from_left + from_right;
}

// The builders take only values and children inside the bound, and they say so in the contract, so the tree they make can be summed.
//@ requires -1000000 <= value && value <= 1000000
//@ ensures result != nullptr && Size(result) == 1 && Sum(result) == value && Within(result, 1000000)
std::unique_ptr<Node> leaf(int32_t value) {
  std::unique_ptr<Node> n = std::make_unique<Node>();
  n->value = value;
  return n;
}

// A parent takes its two children by value and moves them in. A parameter in a contract is its value on entry.
//@ requires -1000000 <= value && value <= 1000000 && Within(left, 1000000) && Within(right, 1000000)
//@ ensures result != nullptr && Size(result) == 1 + Size(left) + Size(right) && Sum(result) == value + Sum(left) + Sum(right)
//@ ensures Within(result, 1000000)
std::unique_ptr<Node> parent(int32_t value, std::unique_ptr<Node> left, std::unique_ptr<Node> right) {
  std::unique_ptr<Node> n = std::make_unique<Node>();
  n->value = value;
  n->left = std::move(left);
  n->right = std::move(right);
  return n;
}

//@ ensures result == 6
int32_t sum_of_three() {
  std::unique_ptr<Node> t = parent(2, leaf(1), leaf(3));
  return sum(t);
}
