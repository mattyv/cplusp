// A division that may divide by zero does not verify, decision 0153. The bound holds, so the divisor is the one fault.
include "../Double.dfy"
import opened Double

method ratio(a: real, b: real) returns (result: real)
  requires abs(a) <= 1.0 && abs(b) <= 1.0
  requires b != 0.0 ==> abs(a / b) <= MAX
{
  result := fdiv(a, b);
}
