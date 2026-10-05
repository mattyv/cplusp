// The ring buffer is a datatype value, decision 0029. The fields are size_t in the C++ and uint64 here, and valid() keeps the capacity
// at most a million, so no sum below leaves uint64. The wrap-around is modular arithmetic on nats. Slot says which place of the seq
// the i-th oldest element is in, and the model of the code writes the same expression in uint64. The lemmas are the facts about
// % that the contracts of push and pop need, since Dafny does not prove nonlinear facts by itself.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

datatype Ring = Ring(items: seq<int32>, head: uint64, count: uint64, capacity: uint64)

predicate Valid(r: Ring) {
  0 < r.capacity <= 1_000_000 && |r.items| == r.capacity as int && r.head < r.capacity && r.count <= r.capacity
}

function Slot(head: nat, i: nat, capacity: nat): nat
  requires capacity > 0
{
  (head + i) % capacity
}

function size(r: Ring): uint64 requires Valid(r) { r.count }

function capacity(r: Ring): uint64 requires Valid(r) { r.capacity }

function at(r: Ring, i: uint64): int32
  requires Valid(r) && i < r.count
{
  r.items[Slot(r.head as int, i as int, r.capacity as int)]
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

method Make(capacity: uint64) returns (r: Ring)
  requires 0 < capacity <= 1_000_000
  ensures Valid(r) && size(r) == 0 && r.capacity == capacity
{
  r := Ring(seq(capacity as int, _ => 0 as int32), 0, 0, capacity);
}

method push(r: Ring, x: int32) returns (r': Ring)
  requires Valid(r) && size(r) < capacity(r)
  ensures Valid(r') && capacity(r') == capacity(r) && size(r') == size(r) + 1
  ensures at(r', size(r') - 1) == x
  ensures forall i :: 0 <= i < size(r) ==> at(r', i) == at(r, i)
{
  var slot: uint64 := (r.head + r.count) % r.capacity;
  r' := Ring(r.items[slot as int := x], r.head, r.count + 1, r.capacity);
  forall i: uint64 | i < r.count
    ensures at(r', i) == at(r, i)
  {
    SlotsDiffer(r.head as int, i as int, r.count as int, r.capacity as int);
  }
}

method pop(r: Ring) returns (r': Ring, result: int32)
  requires Valid(r) && size(r) > 0
  ensures Valid(r') && capacity(r') == capacity(r) && size(r') == size(r) - 1
  ensures result == at(r, 0)
  ensures forall i :: 0 <= i < size(r') ==> at(r', i) == at(r, i + 1)
{
  SlotZero(r.head as int, r.capacity as int);
  result := r.items[r.head];
  r' := Ring(r.items, (r.head + 1) % r.capacity, r.count - 1, r.capacity);
  forall i: uint64 | i < r'.count
    ensures at(r', i) == at(r, i + 1)
  {
    SlotsShift(r.head as int, i as int, r.capacity as int);
  }
}

method first_in_first_out() returns (result: int32)
  ensures result == 123
{
  var r := Make(2);
  r := push(r, 1);
  r := push(r, 2);
  var a: int32;
  r, a := pop(r);
  r := push(r, 3);
  var b: int32;
  r, b := pop(r);
  var c: int32;
  r, c := pop(r);
  result := a * 100 + b * 10 + c;
}
