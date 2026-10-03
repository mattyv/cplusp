// Model B: `find` is an Option<nat>. None is npos, and npos + 1 wraps to 0, so the model has a case for each.
// The postcondition says what the C++ does in both. A C++ that wants the position tests `!= std::string::npos` first.
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

datatype Option<T> = None | Some(value: T)

function Find(s: string, c: char): (r: Option<nat>)
  ensures r.Some? ==> r.value < |s| && s[r.value] == c
  decreases |s|
{
  if |s| == 0 then None
  else if s[0] == c then Some(0)
  else match Find(s[1..], c) {
    case Some(i) => Some(i + 1)
    case None => None
  }
}

method after(s: string) returns (result: uint64)
  requires |s| < 0x1_0000_0000_0000_0000
  ensures Find(s, 'z').Some? ==> result as int == Find(s, 'z').value + 1
  ensures Find(s, 'z').None? ==> result == 0
{
  match Find(s, 'z') {
    case Some(i) => result := (i + 1) as uint64;
    case None => result := 0;
  }
}
