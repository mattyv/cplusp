// Dafny does not prove a nonlinear fact by itself. The lemmas of example.dfy show that a row below rows and a column below cols give
// an index below rows * cols, and where the corner is. At is the element at row i and column j. Its body applies the first lemma, so
// a contract that names it is in range where Dafny checks the contract, as the ensures of at in example.dfy is.
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

function At(m: seq<int32>, rows: int, cols: int, i: int, j: int): int
  requires 0 <= i < rows && 0 <= j < cols && |m| == rows * cols
{
  IndexBelowSize(i, j, rows, cols);
  m[i * cols + j] as int
}
