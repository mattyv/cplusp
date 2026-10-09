// Sum is the specification, the sum of the bytes with no modulus. It is a nat, so a contract knows that it is not negative.
function Sum(s: seq<uint8>): nat
  decreases |s|
{
  if |s| == 0 then 0 else Sum(s[..|s| - 1]) + s[|s| - 1] as nat
}
