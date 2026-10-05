#include <cstddef>
#include <cstdint>
#include <vector>

// A matrix in one vector, row by row. The element at row i and column j is at i * cols + j. The index is an unsigned product and sum,
// and unsigned arithmetic wraps, so the contract says the result fits in a size_t: that is the overflow precondition, written on the
// exact integers. at() takes the shape as parameters. The vector holds rows * cols elements, and the product in the contract is the
// exact one, so a caller cannot make it wrap. From a row below rows and a column below cols the prover proves that the index is
// below the size of the vector. That is the proof the caller of v[i][j] on a vector of vectors never gets.
//@ requires j < cols
//@ requires i * cols + j <= 0xFFFFFFFFFFFFFFFF
//@ ensures result == i * cols + j
size_t index(size_t i, size_t j, size_t cols) {
  return i * cols + j;
}

//@ requires i < rows && j < cols && m.size() == rows * cols
//@ ensures result == m[i * cols + j]
int32_t at(const std::vector<int32_t>& m, size_t rows, size_t cols, size_t i, size_t j) {
  return m[index(i, j, cols)];
}

// A verified caller: the last element of a matrix is its bottom right corner.
//@ requires rows > 0 && cols > 0 && m.size() == rows * cols
//@ ensures result == m[m.size() - 1]
int32_t corner(const std::vector<int32_t>& m, size_t rows, size_t cols) {
  return at(m, rows, cols, rows - 1, cols - 1);
}
