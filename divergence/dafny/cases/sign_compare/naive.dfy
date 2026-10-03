// Model A: Dafny will not compare an int32 with a uint64, so the model converts both to int and compares.
// That is the comparison the contract means. It is not the comparison C++ makes.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method below(i: int32, n: uint64) returns (result: bool)
  ensures result == ((i as int) < (n as int))
{
  result := (i as int) < (n as int);
}

// The model proves true. C++ gives false.
method Demo() {
  var r := below(-1, 1);
  assert r;
}
