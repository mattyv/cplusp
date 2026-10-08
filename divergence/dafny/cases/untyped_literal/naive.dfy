// Model A: the literals as written. With no typed operand, Dafny reads them as exact integers, so the sum cannot overflow.
method positive() returns (result: bool)
  ensures result
{
  result := 2147483647 + 1 > 0;
}
