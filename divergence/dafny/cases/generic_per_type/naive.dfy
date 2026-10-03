// Model A: the template is a generic method, with the type parameter T carried over.
// Dafny cannot multiply a T. The generic method has no arithmetic, so the file is a type error.
method twice<T>(x: T) returns (result: T)
  ensures result == 2 * x
{
  result := 2 * x;
}
