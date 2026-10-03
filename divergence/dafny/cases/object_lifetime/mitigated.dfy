// Model B: the holder keeps the value, as the C++ does under the rule. No pointer, so nothing can outlive its object.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Holder = Holder(v: int32)

method read_later() returns (result: int32)
  ensures result == 42
{
  var h := Holder(0);
  var local: int32 := 42;
  h := h.(v := local);
  result := h.v;
}
