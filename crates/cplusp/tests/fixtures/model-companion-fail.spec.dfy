lemma Positive(x: int)
  ensures x > 0
{
}

lemma Asserted(x: int)
{
  assert x > 0;
}
