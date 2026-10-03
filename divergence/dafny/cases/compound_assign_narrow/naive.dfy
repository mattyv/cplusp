// Model A: `a += 100` as `a := a + 100` on uint8. A Dafny parameter cannot be assigned, so the model uses a local.
// The sum is a range error when a > 155.
newtype uint8 = x: int | 0 <= x < 0x100

method bump(a: uint8) returns (result: uint8)
  ensures result as int == ((a as int) + 100) % 0x100
{
  var b := a;
  b := b + 100;
  result := b;
}
