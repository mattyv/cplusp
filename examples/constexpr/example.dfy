// scaled is pure, so it is a function. constexpr changes nothing in the model, and a constexpr constant is a const. A call at run
// time is the same call. The bound on x keeps the product inside int32.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

const kScale: int32 := 10

function scaled(x: int32): int32
  requires -0x7FFFFF <= x <= 0x7FFFFF
  ensures scaled(x) == x * kScale
{
  x * kScale
}

method scaled_sum(a: int32, b: int32) returns (result: int32)
  requires -0x7FFFFF <= a <= 0x7FFFFF
  requires -0x7FFFFF <= b <= 0x7FFFFF
  ensures result as int == (a as int + b as int) * kScale as int
{
  result := scaled(a) + scaled(b);
}
