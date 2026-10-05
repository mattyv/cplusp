// The two trusted functions are methods with no body, axioms that state the contracts, and the global is a field of the State value
// that each of them takes in and gives back, decision 0029. Valid is the predicate the C++ calls valid(). The callers are real methods,
// and Dafny proves their contracts from the axioms alone. The pool and its allocation are not in the model, since the contracts do not
// need them.
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

datatype State = State(used: uint64)

predicate Valid(s: State) { s.used <= 4096 }

method {:axiom} acquire(s: State, size: uint64) returns (s': State, result: uint64)
  requires Valid(s) && 0 < size && size as int <= 4096 - s.used as int
  ensures Valid(s') && result == s.used && s'.used as int == s.used as int + size as int

method {:axiom} release(s: State) returns (s': State)
  ensures Valid(s') && s'.used == 0

method second_block(s: State, n: uint64, m: uint64) returns (s': State, result: uint64)
  requires Valid(s) && 0 < n && 0 < m && n as int + m as int <= 4096 - s.used as int
  ensures Valid(s') && result as int == s.used as int + n as int && s'.used as int == s.used as int + n as int + m as int
{
  var first: uint64;
  s', first := acquire(s, n);
  s', result := acquire(s', m);
}

method first_block_of_new_frame(s: State, size: uint64) returns (s': State, result: uint64)
  requires 0 < size <= 4096
  ensures result == 0 && s'.used == size && Valid(s')
{
  s' := release(s);
  s', result := acquire(s', size);
}
