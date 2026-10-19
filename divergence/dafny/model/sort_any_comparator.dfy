// A comparator that is not a strict weak order does not verify, decision 0160. With no such requirement, the contract of the
// sort would let this method prove false.
include "../Algorithm.dfy"
import opened Algorithm

method any(v: seq<int>) returns (r: seq<int>)
  requires |v| == 2 && v[0] < v[1]
{
  r := StdSort(v, (a: int, b: int) => true);
  assert false;
}
