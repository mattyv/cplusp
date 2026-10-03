// Model A: the translator maps int32_t to Dafny's int, which has no bounds.
method add(a: int, b: int) returns (result: int)
  ensures result == a + b
{
  result := a + b;
}
