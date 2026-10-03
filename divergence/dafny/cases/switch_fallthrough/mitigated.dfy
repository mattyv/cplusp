// Model B: every case of the C++ ends in a break, so the match is exact.
// The C++ writes `r = 3` in case 1, where it meant the fall-through, and the contract says 3.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method steps(k: int32) returns (result: int32)
  ensures result == (if k == 1 then 3 else if k == 2 then 2 else -1)
{
  var r: int32 := 0;
  match k {
    case 1 => r := 3;
    case 2 => r := r + 2;
    case _ => r := -1;
  }
  result := r;
}
