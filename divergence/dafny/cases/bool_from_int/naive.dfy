// Model A: the C++ is `return x;`, and Dafny has no implicit conversion from int32 to bool.
// The literal line is a type error. Dafny says: "RHS (of type int32) not assignable to LHS (of type bool)".
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method nonzero(x: int32) returns (result: bool)
  ensures result == (x != 0)
{
  result := x;
}
