// Model A: a switch is a match with one arm per case.
// A match arm never runs into the next one, so k == 1 gives 1. The model proves the contract.
// The C++ runs into case 2 and gives 3.
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
