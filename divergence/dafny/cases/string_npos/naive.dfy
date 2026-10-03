// Model A: `find` returns the index of the match, and it has the precondition that there is one.
// The method leaves out `requires 'z' in s`, so Dafny refuses the call to find. It fails.
// The C++ has no such precondition. A string without 'z' gives npos.
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

function Find(s: string, c: char): (i: nat)
  requires c in s
  ensures i < |s| && s[i] == c
  decreases |s|
{
  if s[0] == c then 0 else 1 + Find(s[1..], c)
}

method after(s: string) returns (result: uint64)
  requires |s| < 0x1_0000_0000_0000_0000
  ensures result as int == Find(s, 'z') + 1
{
  result := (Find(s, 'z') + 1) as uint64;
}
