// A span is a seq, and std::optional<size_t> is an Option of uint64. The contract and the invariants are the C++ ones. The midpoint is
// lo + (hi - lo) / 2, and Dafny proves that it does not overflow from lo <= hi alone. With (lo + hi) / 2 it asks for a bound on the sum
// that the length of the seq does not give. The first invariant bounds the pair, and decreases shows that the window shrinks.
// A span has a size_t length, so the model of a span is a seq shorter than 2^64, as in custom_range.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

type Span = s: seq<int32> | |s| < 0x1_0000_0000_0000_0000 witness []

datatype Option<T> = None | Some(value: T)

method binary_search(a: Span, key: int32) returns (result: Option<uint64>)
  requires forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
  ensures result.Some? ==> result.value as int < |a| && a[result.value] == key
  ensures result.None? ==> forall i :: 0 <= i < |a| ==> a[i] != key
{
  var lo: uint64 := 0;
  var hi: uint64 := |a| as uint64;
  while lo < hi
    invariant lo <= hi && hi as int <= |a|
    invariant forall i :: 0 <= i < lo as int ==> a[i] < key
    invariant forall i :: hi as int <= i < |a| ==> a[i] > key
    decreases hi - lo
  {
    var mid: uint64 := lo + (hi - lo) / 2;
    if a[mid] < key {
      lo := mid + 1;
    } else if a[mid] > key {
      hi := mid;
    } else {
      return Some(mid);
    }
  }
  return None;
}

method contains(a: Span, key: int32) returns (result: bool)
  requires forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
  ensures result == exists i :: 0 <= i < |a| && a[i] == key
{
  var r := binary_search(a, key);
  result := r.Some?;
}
