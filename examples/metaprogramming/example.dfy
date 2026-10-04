// The trusted function is a method with no body, an axiom that states a plain contract. The template does not appear in the
// model. The caller calls the plain function twice, and Dafny proves that the second call is in range.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method {:axiom} twice32(x: int32) returns (result: int32)
  requires -0x4000_0000 <= x < 0x4000_0000
  ensures result as int == 2 * (x as int)

method quadruple(x: int32) returns (result: int32)
  requires -0x1000_0000 <= x < 0x1000_0000
  ensures result as int == 4 * (x as int)
{
  var t := twice32(x);
  result := twice32(t);
}
