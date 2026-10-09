// The identity.
function Id(y: int): int
{
  y
}

// A lemma whose body holds a forall statement with no body, which states a false fact with no proof.
lemma Anything(x: int)
  ensures x > 0
{
  forall y: int
    ensures Id(y) > y
  assert Id(x) > x;
}
