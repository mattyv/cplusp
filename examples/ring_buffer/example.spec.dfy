// The facts about % that the contracts of push and pop need, since Dafny does not prove nonlinear facts by itself. Slot i is
// (head + i) % capacity, as the code computes it. Each fact for all slots is a lemma that push or pop applies, decision 0167.
function Slot(head: nat, i: nat, capacity: nat): nat
  requires capacity > 0
{
  (head + i) % capacity
}

lemma NonnegProduct(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures a * b >= 0
  decreases a
{
  if a > 0 {
    NonnegProduct(a - 1, b);
  }
}

// The division axiom of Dafny, said as a lemma, so that the proofs below name the quotient.
lemma DivMod(x: nat, m: nat)
  requires m > 0
  ensures x == (x / m) * m + x % m && 0 <= x % m < m
{
}

lemma AtLeastOne(k: int, m: int)
  requires k >= 1 && m > 0
  ensures k * m >= m
{
  NonnegProduct(k - 1, m);
  assert (k - 1) * m == k * m - m;
}

// A remainder is the only value in [0, m) that differs from x by a multiple of m.
lemma ModUnique(x: nat, q: nat, r: nat, m: nat)
  requires m > 0 && r < m && x == q * m + r
  ensures x % m == r
{
  DivMod(x, m);
  var q0 := x / m;
  if q0 < q {
    AtLeastOne(q - q0, m);
    assert (q - q0) * m == q * m - q0 * m;
  } else if q0 > q {
    AtLeastOne(q0 - q, m);
    assert (q0 - q) * m == q0 * m - q * m;
  }
}

// Two places less than a capacity apart are two different slots.
lemma SlotsDiffer(head: nat, i: nat, j: nat, capacity: nat)
  requires capacity > 0 && i < j < capacity
  ensures Slot(head, i, capacity) != Slot(head, j, capacity)
{
  DivMod(head + i, capacity);
  DivMod(head + j, capacity);
  var qi := (head + i) / capacity;
  var qj := (head + j) / capacity;
  if Slot(head, i, capacity) == Slot(head, j, capacity) {
    if qj <= qi {
      NonnegProduct(qi - qj, capacity);
      assert (qi - qj) * capacity == qi * capacity - qj * capacity;
    } else {
      AtLeastOne(qj - qi, capacity);
      assert (qj - qi) * capacity == qj * capacity - qi * capacity;
    }
  }
}

// The first place from the head is the head itself.
lemma SlotZero(head: nat, capacity: nat)
  requires capacity > 0 && head < capacity
  ensures Slot(head, 0, capacity) == head
{
  ModUnique(head, 0, head, capacity);
}

// Moving the head on by one moves every slot on by one.
lemma SlotsShift(head: nat, i: nat, capacity: nat)
  requires capacity > 0 && head < capacity
  ensures Slot((head + 1) % capacity, i, capacity) == Slot(head, i + 1, capacity)
{
  DivMod(head + 1, capacity);
  var q := (head + 1) / capacity;
  var r := (head + 1) % capacity;
  DivMod(r + i, capacity);
  var q2 := (r + i) / capacity;
  ModUnique(head + i + 1, q + q2, (r + i) % capacity, capacity);
}

// The model writes % of two sizes as trunc_rem. Each fact for all slots names the slot k itself, so that the prover can match
// it to each slot of the code. The slot of the next push differs from the slot of each element, so a push keeps each element.
lemma SlotsDifferAll(head: nat, count: nat, capacity: nat)
  requires capacity > 0 && count < capacity
  ensures forall k :: head <= k < head + count ==> trunc_rem(k, capacity) != trunc_rem(head + count, capacity)
{
  forall k | head <= k < head + count
    ensures trunc_rem(k, capacity) != trunc_rem(head + count, capacity)
  {
    SlotsDiffer(head, k - head, count, capacity);
  }
}

// After a pop, the slot of element i is the old slot of element i + 1, and the old head is slot 0.
lemma SlotsShiftAll(head: nat, capacity: nat)
  requires capacity > 0 && head < capacity
  ensures forall k :: trunc_rem(head + 1, capacity) <= k ==> trunc_rem(k, capacity) == trunc_rem(k - trunc_rem(head + 1, capacity) + head + 1, capacity)
  ensures trunc_rem(head, capacity) == head
{
  forall k | trunc_rem(head + 1, capacity) <= k
    ensures trunc_rem(k, capacity) == trunc_rem(k - trunc_rem(head + 1, capacity) + head + 1, capacity)
  {
    SlotsShift(head, k - trunc_rem(head + 1, capacity), capacity);
  }
  SlotZero(head, capacity);
}
