// Each operation of the model carries its bound and its error, decision 0153. A method with the bound proves the error of one
// rounding with no call of the axiom.
include "../Double.dfy"
import opened Double

method product(a: real, b: real) returns (result: real)
  requires abs(a * b) <= MAX
  ensures abs(result - a * b) <= EPS * abs(a * b) + ETA
{
  result := fmul(a, b);
}

method ratio(a: real, b: real) returns (result: real)
  requires b != 0.0 && abs(a / b) <= MAX
  ensures abs(result - a / b) <= EPS * abs(a / b) + ETA
{
  result := fdiv(a, b);
}

method sum(a: real, b: real) returns (result: real)
  requires abs(a + b) <= MAX
  ensures abs(result - (a + b)) <= EPS * abs(a + b) + ETA
{
  result := fadd(a, b);
}

method difference(a: real, b: real) returns (result: real)
  requires abs(a - b) <= MAX
  ensures abs(result - (a - b)) <= EPS * abs(a - b) + ETA
{
  result := fsub(a, b);
}
