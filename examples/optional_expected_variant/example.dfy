// An optional is a datatype with None and Some. `*h` is `h.value`, and Dafny asks for a proof that h is Some, which the has_value
// test gives. C++ division and remainder round toward zero and Dafny rounds down, so the model uses trunc_div and trunc_rem.
// A variant is a datatype with one constructor for each alternative. A read of an alternative needs a proof that it is held.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Option<T> = None | Some(value: T)

datatype Alt = AnInt(i: int32) | ABool(b: bool)

function abs(x: int): int {
  if x < 0 then -x else x
}

function trunc_div(a: int, b: int): int
  requires b != 0
{
  var q := abs(a) / abs(b);
  if (a < 0) != (b < 0) then -q else q
}

function trunc_rem(a: int, b: int): int
  requires b != 0
{
  var r := abs(a) % abs(b);
  if a < 0 then -r else r
}

method half_of_even(x: int32) returns (result: Option<int32>)
  ensures result.Some? == (trunc_rem(x as int, 2) == 0)
  ensures result.Some? ==> result.value as int == trunc_div(x as int, 2)
{
  if trunc_rem(x as int, 2) != 0 {
    result := None;
  } else {
    result := Some(trunc_div(x as int, 2) as int32);
  }
}

method half_or(x: int32, fallback: int32) returns (result: int32)
  ensures result as int == (if trunc_rem(x as int, 2) == 0 then trunc_div(x as int, 2) else fallback as int)
{
  var h := half_of_even(x);
  if !h.Some? {
    return fallback;
  }
  return h.value;
}

method as_int(v: Alt) returns (result: int32)
  requires v.AnInt?
  ensures result == v.i
{
  result := v.i;
}

method int_or_zero(v: Alt) returns (result: int32)
  ensures result == (if v.AnInt? then v.i else 0)
{
  if !v.AnInt? {
    return 0;
  }
  result := as_int(v);
}
