// A move-only handle is a datatype, decision 0029. The global count is a State value every function takes in and gives back.
// The model has no destructor, so Destroy is called where the block ends, once for every handle the C++ would destroy, the
// closed one too. A move is a copy, and the source becomes closed. Destroy of a closed handle releases nothing, as in the C++.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype State = State(open_count: int32)

datatype Handle = Handle(open: bool)

predicate Valid(h: Handle) { h.open }

method MakeHandle(s: State) returns (s': State, h: Handle)
  requires 0 <= s.open_count < 1000
  ensures Valid(h) && s'.open_count == s.open_count + 1
{
  s' := State(s.open_count + 1);
  h := Handle(true);
}

method MoveHandle(other: Handle) returns (other': Handle, h: Handle)
  requires Valid(other)
  ensures Valid(h) && !Valid(other')
{
  h := other;
  other' := Handle(false);
}

method Destroy(s: State, h: Handle) returns (s': State)
  requires 0 <= s.open_count <= 1000
  ensures s'.open_count == s.open_count - (if Valid(h) then 1 else 0)
{
  if h.open {
    s' := State(s.open_count - 1);
  } else {
    s' := s;
  }
}

method count_inside_block(s: State) returns (s': State, result: int32)
  requires 0 <= s.open_count < 1000
  ensures s'.open_count == s.open_count && result == s.open_count + 1
{
  var inside: int32 := 0;
  var h: Handle;
  s', h := MakeHandle(s);
  inside := s'.open_count;
  s' := Destroy(s', h);
  result := inside;
}

method consume(s: State, h: Handle) returns (s': State, h': Handle)
  requires Valid(h) && 0 < s.open_count <= 1000
  ensures s'.open_count == s.open_count - 1 && !Valid(h')
{
  var owned: Handle;
  h', owned := MoveHandle(h);
  s' := Destroy(s, owned);
}

method hand_over(s: State) returns (s': State)
  requires 0 <= s.open_count < 1000
  ensures s'.open_count == s.open_count
{
  var h: Handle;
  s', h := MakeHandle(s);
  s', h := consume(s', h);
  s' := Destroy(s', h);
}
