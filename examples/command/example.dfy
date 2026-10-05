// A command has state, so the driver changes the vector that owns the commands, and in the model the vector is a seq of Option
// values that goes in and comes out, decision 0029. The interface is an opaque type with its contract. A call that changes a command
// takes the command in and gives it back, and the driver puts the new command into the seq at the same index, so a call on one
// command leaves every other command as it was. The calls on the interface are methods without a body. Each class proves its own
// contract on its own datatype, and meets the contract of the interface with a stronger one. The conversions to the interface say
// only what a const function reads, and are trusted, as the vtables are.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Option<T> = None | Some(value: T)

datatype Counter = Counter(n: int32)

predicate ValidCounter(c: Counter) { 0 <= c.n <= 1000 }

function value(c: Counter): int32 { c.n }

method MakeCounter(start: int32) returns (c: Counter)
  requires 0 <= start <= 1000
  ensures ValidCounter(c) && value(c) == start
{
  c := Counter(start);
}

method assign(c: Counter, v: int32) returns (c': Counter)
  requires ValidCounter(c) && 0 <= v <= 1000
  ensures ValidCounter(c') && value(c') == v
{
  c' := Counter(v);
}

type Command

predicate {:axiom} ValidCmd(k: Command)

predicate {:axiom} done(k: Command)

function {:axiom} before(k: Command): int32
  requires ValidCmd(k) && done(k)
  ensures 0 <= before(k) <= 1000

method {:axiom} execute(k: Command, c: Counter) returns (k': Command, c': Counter)
  requires ValidCmd(k) && !done(k) && ValidCounter(c) && value(c) < 1000
  ensures ValidCmd(k') && done(k') && ValidCounter(c') && before(k') == value(c) && value(c') <= value(c) + 1

method {:axiom} undo(k: Command, c: Counter) returns (k': Command, c': Counter)
  requires ValidCmd(k) && done(k) && ValidCounter(c)
  ensures ValidCmd(k') && !done(k') && ValidCounter(c') && value(c') == before(k)

// The first command. The override check is the contract of each method: it keeps every promise of the interface, and its
// promise about the counter is stronger.
datatype Increment = Increment(done_: bool, before_: int32)

predicate ValidIncrement(i: Increment) { !i.done_ || 0 <= i.before_ <= 1000 }

method MakeIncrement() returns (i: Increment)
  ensures ValidIncrement(i) && !i.done_
{
  i := Increment(false, 0);
}

function increment_before(i: Increment): int32
  requires ValidIncrement(i) && i.done_
  ensures increment_before(i) == i.before_
{
  i.before_
}

method increment_execute(i: Increment, c: Counter) returns (i': Increment, c': Counter)
  requires ValidIncrement(i) && !i.done_ && ValidCounter(c) && value(c) < 1000
  ensures ValidIncrement(i') && i'.done_ && ValidCounter(c') && i'.before_ == value(c) && value(c') == value(c) + 1
{
  var i1 := i.(before_ := value(c));
  c' := assign(c, i1.before_ + 1);
  i' := i1.(done_ := true);
}

method increment_undo(i: Increment, c: Counter) returns (i': Increment, c': Counter)
  requires ValidIncrement(i) && i.done_ && ValidCounter(c)
  ensures ValidIncrement(i') && !i'.done_ && ValidCounter(c') && value(c') == i.before_
{
  c' := assign(c, i.before_);
  i' := i.(done_ := false);
}

function {:axiom} IncrementAsCommand(i: Increment): Command
  ensures ValidCmd(IncrementAsCommand(i)) == ValidIncrement(i)
  ensures done(IncrementAsCommand(i)) == i.done_
  ensures ValidIncrement(i) && i.done_ ==> before(IncrementAsCommand(i)) == increment_before(i)

// The second command.
datatype Reset = Reset(done_: bool, before_: int32)

predicate ValidReset(r: Reset) { !r.done_ || 0 <= r.before_ <= 1000 }

method MakeReset() returns (r: Reset)
  ensures ValidReset(r) && !r.done_
{
  r := Reset(false, 0);
}

function reset_before(r: Reset): int32
  requires ValidReset(r) && r.done_
  ensures reset_before(r) == r.before_
{
  r.before_
}

method reset_execute(r: Reset, c: Counter) returns (r': Reset, c': Counter)
  requires ValidReset(r) && !r.done_ && ValidCounter(c) && value(c) < 1000
  ensures ValidReset(r') && r'.done_ && ValidCounter(c') && r'.before_ == value(c) && value(c') == 0
{
  var r1 := r.(before_ := value(c));
  c' := assign(c, 0);
  r' := r1.(done_ := true);
}

method reset_undo(r: Reset, c: Counter) returns (r': Reset, c': Counter)
  requires ValidReset(r) && r.done_ && ValidCounter(c)
  ensures ValidReset(r') && !r'.done_ && ValidCounter(c') && value(c') == r.before_
{
  c' := assign(c, r.before_);
  r' := r.(done_ := false);
}

function {:axiom} ResetAsCommand(r: Reset): Command
  ensures ValidCmd(ResetAsCommand(r)) == ValidReset(r)
  ensures done(ResetAsCommand(r)) == r.done_
  ensures ValidReset(r) && r.done_ ==> before(ResetAsCommand(r)) == reset_before(r)

method run_and_undo(cmds0: seq<Option<Command>>, c0: Counter) returns (cmds: seq<Option<Command>>, c: Counter)
  requires |cmds0| <= 100
  requires forall j :: 0 <= j < |cmds0| ==> cmds0[j].Some?
  requires forall j :: 0 <= j < |cmds0| ==> ValidCmd(cmds0[j].value) && !done(cmds0[j].value)
  requires ValidCounter(c0) && value(c0) <= 900
  ensures ValidCounter(c) && value(c) == value(c0)
  ensures |cmds| == |cmds0|
  ensures forall j :: 0 <= j < |cmds| ==> cmds[j].Some? && ValidCmd(cmds[j].value) && !done(cmds[j].value)
{
  var n := |cmds0|;
  cmds := cmds0;
  c := c0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n && n == |cmds|
    invariant ValidCounter(c) && value(c) as int <= value(c0) as int + i
    invariant i == 0 ==> c == c0
    invariant forall j :: 0 <= j < n ==> cmds[j].Some?
    invariant forall j :: 0 <= j < i ==> ValidCmd(cmds[j].value) && done(cmds[j].value)
    invariant forall j :: i <= j < n ==> ValidCmd(cmds[j].value) && !done(cmds[j].value)
    invariant i > 0 ==> before(cmds[0].value) == value(c0)
    decreases n - i
  {
    var k: Command;
    k, c := execute(cmds[i].value, c);
    cmds := cmds[i := Some(k)];
    i := i + 1;
  }
  i := n;
  while i > 0
    invariant 0 <= i <= n && n == |cmds| && ValidCounter(c)
    invariant forall j :: 0 <= j < n ==> cmds[j].Some?
    invariant forall j :: 0 <= j < i ==> ValidCmd(cmds[j].value) && done(cmds[j].value)
    invariant forall j :: i <= j < n ==> ValidCmd(cmds[j].value) && !done(cmds[j].value)
    invariant i > 0 ==> before(cmds[0].value) == value(c0)
    invariant i == 0 ==> value(c) == value(c0)
    decreases i
  {
    var k: Command;
    k, c := undo(cmds[i - 1].value, c);
    cmds := cmds[i - 1 := Some(k)];
    i := i - 1;
  }
}

method demo() returns (result: int32)
  ensures result == 5
{
  var c := MakeCounter(5);
  var a := MakeIncrement();
  var r := MakeReset();
  var b := MakeIncrement();
  var cmds: seq<Option<Command>> := [Some(IncrementAsCommand(a)), Some(ResetAsCommand(r)), Some(IncrementAsCommand(b))];
  cmds, c := run_and_undo(cmds, c);
  result := value(c);
}
