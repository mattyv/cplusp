// The trusted function is a method with no body, an axiom that states its contract. A unique_ptr is an Option value, decision 0029,
// and the contract says the box is Some and holds x. The caller proves its result from that.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Option<T> = None | Some(value: T)

method {:axiom} make_box(x: int32) returns (result: Option<int32>)
  ensures result.Some? && result.value == x

method doubled(x: int32) returns (result: int32)
  requires -0x4000_0000 <= x < 0x4000_0000
  ensures result as int == 2 * (x as int)
{
  var b := make_box(x);
  result := b.value + b.value;
}
