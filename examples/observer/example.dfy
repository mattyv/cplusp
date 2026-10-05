// The subject owns its observers, so it is a datatype that holds a seq of Option values, as a vector of unique_ptr is, decision 0029.
// The interface is an opaque type with its contract, and the call that changes an observer is a method without a body that takes the
// observer in and gives it back. The subject puts the new observer into the seq at the same index, so a call on one observer leaves
// every other observer as it was. The invariant is a predicate over the seq. The C++ computes it with a loop, and valid_check proves
// that the loop returns the predicate. Each class proves its own contract on its own datatype. The conversions to the interface say
// only what a const function reads, and are trusted, as the vtables are.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

datatype Option<T> = None | Some(value: T)

type Observer

predicate {:axiom} ValidObserver(o: Observer)

function {:axiom} seen(o: Observer): int32
  requires ValidObserver(o)
  ensures 0 <= seen(o) <= 1000

method {:axiom} on_change(o: Observer, v: int32) returns (o': Observer)
  requires ValidObserver(o) && seen(o) < 1000
  ensures ValidObserver(o') && seen(o') == seen(o) + 1

datatype Tally = Tally(seen_: int32)

predicate ValidTally(t: Tally) { 0 <= t.seen_ <= 1000 }

method MakeTally() returns (t: Tally)
  ensures ValidTally(t) && t.seen_ == 0
{
  t := Tally(0);
}

method tally_on_change(t: Tally, v: int32) returns (t': Tally)
  requires ValidTally(t) && t.seen_ < 1000
  ensures ValidTally(t') && t'.seen_ == t.seen_ + 1
{
  t' := Tally(t.seen_ + 1);
}

function {:axiom} TallyAsObserver(t: Tally): Observer
  ensures ValidObserver(TallyAsObserver(t)) == ValidTally(t)
  ensures ValidTally(t) ==> seen(TallyAsObserver(t)) == t.seen_

datatype Latest = Latest(seen_: int32, last_: int32)

predicate ValidLatest(l: Latest) { 0 <= l.seen_ <= 1000 }

method MakeLatest() returns (l: Latest)
  ensures ValidLatest(l) && l.seen_ == 0 && l.last_ == 0
{
  l := Latest(0, 0);
}

method latest_on_change(l: Latest, v: int32) returns (l': Latest)
  requires ValidLatest(l) && l.seen_ < 1000
  ensures ValidLatest(l') && l'.seen_ == l.seen_ + 1 && l'.last_ == v
{
  l' := Latest(l.seen_ + 1, v);
}

function {:axiom} LatestAsObserver(l: Latest): Observer
  ensures ValidObserver(LatestAsObserver(l)) == ValidLatest(l)
  ensures ValidLatest(l) ==> seen(LatestAsObserver(l)) == l.seen_

datatype Subject = Subject(observers_: seq<Option<Observer>>, value_: int32)

predicate ValidSubject(s: Subject) {
  |s.observers_| <= 100 && forall i :: 0 <= i < |s.observers_| ==> s.observers_[i].Some? && ValidObserver(s.observers_[i].value)
}

method valid_check(s: Subject) returns (result: bool)
  ensures result == ValidSubject(s)
{
  if |s.observers_| > 100 {
    return false;
  }
  var i := 0;
  while i < |s.observers_|
    invariant 0 <= i <= |s.observers_|
    invariant forall j :: 0 <= j < i ==> s.observers_[j].Some? && ValidObserver(s.observers_[j].value)
    decreases |s.observers_| - i
  {
    if !s.observers_[i].Some? || !ValidObserver(s.observers_[i].value) {
      return false;
    }
    i := i + 1;
  }
  return true;
}

method MakeSubject() returns (s: Subject)
  ensures ValidSubject(s) && |s.observers_| == 0 && s.value_ == 0
{
  s := Subject([], 0);
}

function observer_count(s: Subject): uint64
  requires ValidSubject(s)
{
  |s.observers_| as uint64
}

function count_of(s: Subject, i: uint64): int32
  requires ValidSubject(s) && i < observer_count(s)
{
  seen(s.observers_[i].value)
}

method attach(s: Subject, o: Option<Observer>) returns (s': Subject)
  requires ValidSubject(s) && observer_count(s) < 100 && o.Some? && ValidObserver(o.value) && seen(o.value) == 0
  ensures ValidSubject(s') && observer_count(s') == observer_count(s) + 1
  ensures forall i: uint64 :: i < observer_count(s) ==> count_of(s', i) == count_of(s, i)
  ensures count_of(s', observer_count(s)) == 0
{
  s' := s.(observers_ := s.observers_ + [o]);
}

method set_value(s: Subject, v: int32) returns (s': Subject)
  requires ValidSubject(s) && forall i: uint64 :: i < observer_count(s) ==> count_of(s, i) < 1000
  ensures ValidSubject(s') && observer_count(s') == observer_count(s) && s'.value_ == v
  ensures forall i: uint64 :: i < observer_count(s') ==> count_of(s', i) == count_of(s, i) + 1
{
  s' := s.(value_ := v);
  forall j | 0 <= j < |s.observers_|
    ensures seen(s.observers_[j].value) < 1000
  {
    assert j as uint64 < observer_count(s);
    assert count_of(s, j as uint64) < 1000;
  }
  var i := 0;
  while i < |s'.observers_|
    invariant 0 <= i <= |s'.observers_| && |s'.observers_| == |s.observers_|
    invariant forall j :: 0 <= j < |s'.observers_| ==> s'.observers_[j].Some? && ValidObserver(s'.observers_[j].value)
    invariant forall j :: 0 <= j < i ==> seen(s'.observers_[j].value) == seen(s.observers_[j].value) + 1
    invariant forall j :: i <= j < |s'.observers_| ==> s'.observers_[j] == s.observers_[j] && seen(s.observers_[j].value) < 1000
    invariant s'.value_ == v
    decreases |s'.observers_| - i
  {
    var o := on_change(s'.observers_[i].value, v);
    s' := s'.(observers_ := s'.observers_[i := Some(o)]);
    i := i + 1;
  }
}

method demo() returns (result: int32)
  ensures result == 6
{
  var s := MakeSubject();
  var t := MakeTally();
  var l := MakeLatest();
  s := attach(s, Some(TallyAsObserver(t)));
  s := attach(s, Some(LatestAsObserver(l)));
  s := set_value(s, 10);
  s := set_value(s, 20);
  s := set_value(s, 30);
  result := count_of(s, 0) + count_of(s, 1);
}
