// A flags type is a bv32, and not a datatype of its enumerators. The C++ underlying type is fixed, so every bit pattern is a value of
// Flag, and Read | Write is one that no enumerator names. A datatype would have no value for it, and a set of enumerators could not hold
// a bit that no enumerator names. The bv32 holds them all, and the bitwise operators of Dafny are the C++ ones on uint32_t. So the
// casts in the C++ need no precondition here, where the rule enum_cast would ask for one on an enum that is no flags type. The
// enumerators are constants. The operators are methods named operator_or and operator_and, since Dafny has no operator names. Only
// has is a function, because the contracts use it.
type Flag = bv32

const None: Flag := 0
const Read: Flag := 1
const Write: Flag := 2
const Exec: Flag := 4
const Admin: Flag := 8

function has(flags: Flag, flag: Flag): bool {
  (flags & flag) == flag
}

method operator_or(a: Flag, b: Flag) returns (result: Flag)
  ensures result == a | b
  ensures has(result, a) && has(result, b)
{
  result := a | b;
}

method operator_and(a: Flag, b: Flag) returns (result: Flag)
  ensures result == a & b
  ensures has(a, result) && has(b, result)
{
  result := a & b;
  // Without these two facts the prover times out. They are plain bit facts: a bit of the overlap is a bit of each side.
  assert (a & result) == result;
  assert (b & result) == result;
}

method grant(flags: Flag, flag: Flag) returns (result: Flag)
  ensures has(result, flag) && (has(flags, Read) ==> has(result, Read))
{
  result := operator_or(flags, flag);
}

method both_may_write(a: Flag, b: Flag) returns (result: bool)
  ensures result == (has(a, Write) && has(b, Write))
{
  var overlap := operator_and(a, b);
  result := has(overlap, Write);
}

method reader_and_writer_cannot_exec() returns (result: bool)
  ensures result == true
{
  var f := operator_or(Read, Write);
  result := has(f, Write) && !has(f, Exec);
}
