// Model A: `base_value` is the constant 5, and `derived` is the constant 6. Both are set before any function runs. The proof goes through.
// In the C++, `derived` has a dynamic initializer in another file. It may run before `base_value` is set, and `read_derived()` may return 1.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

const base_value: int32 := 5
const derived: int32 := 6

method read_derived() returns (result: int32)
  ensures result == base_value + 1
{
  result := derived;
}
