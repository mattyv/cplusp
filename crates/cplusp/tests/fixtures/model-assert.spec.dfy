// Sum is the sum of the bytes with no modulus. It is a nat, so a contract knows that it is not negative.
function Sum(s: seq<uint8>): nat
  decreases |s|
{
  if |s| == 0 then 0 else Sum(s[..|s| - 1]) + s[|s| - 1] as nat
}

// The sum of a prefix one longer adds the next byte.
lemma SumStep(s: seq<uint8>, i: int)
  requires 0 <= i < |s|
  ensures Sum(s[..i + 1]) == Sum(s[..i]) + s[i] as nat
{
  assert s[..i + 1][..i] == s[..i];
}

// The prefix of the full length is the sequence.
lemma SumAll(s: seq<uint8>)
  ensures Sum(s[..|s|]) == Sum(s)
{
  assert s[..|s|] == s;
}
