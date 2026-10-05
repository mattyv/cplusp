// A vector is a seq shorter than 2^64, as in custom_range. The index is the exact integer i * cols + j, and the precondition of index
// keeps it below 2^64, so the uint64 arithmetic does not wrap. Dafny does not prove a nonlinear fact by itself. The lemma shows that a
// row below rows and a column below cols give an index below rows * cols, by the one product that is not negative. The ensures of at
// calls it first, so that Dafny sees the index in range where it checks the contract itself.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

type Items = s: seq<int32> | |s| < 0x1_0000_0000_0000_0000 witness []

lemma NonnegProduct(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures a * b >= 0
  decreases a
{
  if a > 0 {
    NonnegProduct(a - 1, b);
  }
}

lemma IndexBelowSize(i: int, j: int, rows: int, cols: int)
  requires 0 <= i < rows && 0 <= j < cols
  ensures 0 <= i * cols + j < rows * cols
{
  NonnegProduct(i, cols);
  NonnegProduct(rows - i - 1, cols);
  assert (rows - i - 1) * cols == rows * cols - i * cols - cols;
}

lemma CornerIndex(rows: int, cols: int)
  requires rows > 0 && cols > 0
  ensures (rows - 1) * cols + (cols - 1) == rows * cols - 1
{
  assert (rows - 1) * cols == rows * cols - cols;
}

method index(i: uint64, j: uint64, cols: uint64) returns (result: uint64)
  requires j < cols
  requires i as int * cols as int + j as int < 0x1_0000_0000_0000_0000
  ensures result as int == i as int * cols as int + j as int
{
  // The product alone is below 2^64 because the sum is, and the prover finds that more surely when it is said.
  assert i as int * cols as int < 0x1_0000_0000_0000_0000;
  result := i * cols + j;
}

method at(m: Items, rows: uint64, cols: uint64, i: uint64, j: uint64) returns (result: int32)
  requires i < rows && j < cols && |m| == rows as int * cols as int
  ensures (IndexBelowSize(i as int, j as int, rows as int, cols as int); result == m[i as int * cols as int + j as int])
{
  IndexBelowSize(i as int, j as int, rows as int, cols as int);
  var k := index(i, j, cols);
  result := m[k];
}

method corner(m: Items, rows: uint64, cols: uint64) returns (result: int32)
  requires rows > 0 && cols > 0 && |m| == rows as int * cols as int
  ensures result == m[|m| - 1]
{
  CornerIndex(rows as int, cols as int);
  result := at(m, rows, cols, rows - 1, cols - 1);
}
