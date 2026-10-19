lemma Both(x: int)
  ensures x > 0
  ensures x < 0
{
}

lemma Needs(x: int)
  requires x > 0
  requires x < 0
{
}
