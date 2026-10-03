// Model A: std::variant<int32_t, bool> as a datatype with one constructor per alternative, and the read as the field.
// Dafny asks for a proof that v holds an int32. There is none, so the model is stricter than C++.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Alt = AnInt(i: int32) | ABool(b: bool)

method as_int(v: Alt) returns (result: int32)
  ensures result == v.i
{
  result := v.i;
}
