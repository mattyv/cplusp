// An enum class is a datatype of its enumerators, and the Result struct is a datatype of its three fields. The switch is a match that
// covers every error. The contract is the same, one line for each case. A square of at most 46340 is below 2^31, so Dafny proves that
// the product does not overflow from the bound, and it would refuse the product without it.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Error = None | Negative | TooBig

datatype Result = Result(ok: bool, error: Error, value: int32)

method checked_square(x: int32) returns (result: Result)
  ensures result.ok == (result.error == None)
  ensures x < 0 ==> !result.ok && result.error == Negative && result.value == 0
  ensures x > 46340 ==> !result.ok && result.error == TooBig && result.value == 0
  ensures 0 <= x <= 46340 ==> result.ok && result.value == x * x
{
  if x < 0 {
    return Result(false, Negative, 0);
  }
  if x > 46340 {
    return Result(false, TooBig, 0);
  }
  return Result(true, None, x * x);
}

method square_or_code(x: int32) returns (result: int32)
  ensures x < 0 ==> result == -1
  ensures x > 46340 ==> result == -2
  ensures 0 <= x <= 46340 ==> result == x * x
{
  var r := checked_square(x);
  match r.error {
    case None => return r.value;
    case Negative => return -1;
    case TooBig => return -2;
  }
}
