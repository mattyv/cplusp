// Model B: the same model as model A. The fixed C++ ends case 1 with a break, so the match is exact for it.
// A match arm never runs into the next one, so k == 1 gives 1, as the fixed C++ does.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method steps(k: int32) returns (result: int32)
  ensures result == (if k == 1 then 1 else if k == 2 then 2 else -1)
{
  var r: int32 := 0;
  match k {
    case 1 => r := 1;
    case 2 => r := r + 2;
    case _ => r := -1;
  }
  result := r;
}
