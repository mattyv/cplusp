// The state interface is an opaque type, decision 0029, and next is a function of the state value, since the C++ method is const.
// It returns an Option of the interface, as a unique_ptr does. Each state class is a datatype that proves the same table on its own
// value, through the phase of the object it makes. The conversions to the interface are trusted, as the vtables are. The context
// holds the current state as an Option and replaces it, so the caller proves its phase from the table of the context alone.
// Compare the folder state_machine, where a state is a datatype and the table is a match.
datatype Phase = Idle | Running | Done
datatype Event = Start | Finish | Reset

datatype Option<T> = None | Some(value: T)

type State

predicate {:axiom} ValidState(s: State)

function {:axiom} phase(s: State): Phase
  requires ValidState(s)

function {:axiom} next(s: State, e: Event): Option<State>
  requires ValidState(s)
  ensures next(s, e).Some? && ValidState(next(s, e).value)
  ensures e == Reset ==> phase(next(s, e).value) == Idle
  ensures phase(s) == Idle && e == Start ==> phase(next(s, e).value) == Running
  ensures phase(s) == Running && e == Finish ==> phase(next(s, e).value) == Done
  ensures e != Reset && !(phase(s) == Idle && e == Start) && !(phase(s) == Running && e == Finish) ==> phase(next(s, e).value) == phase(s)

datatype IdleState = IdleState
datatype RunningState = RunningState
datatype DoneState = DoneState

function {:axiom} IdleAsState(q: IdleState): State
  ensures ValidState(IdleAsState(q)) && phase(IdleAsState(q)) == Idle

function {:axiom} RunningAsState(q: RunningState): State
  ensures ValidState(RunningAsState(q)) && phase(RunningAsState(q)) == Running

function {:axiom} DoneAsState(q: DoneState): State
  ensures ValidState(DoneAsState(q)) && phase(DoneAsState(q)) == Done

// The override check. Each class keeps the table of the interface, in the terms of the phases of the objects it makes.
// The body of each function calls the conversions of the other classes, so a conversion cannot name the function in its own
// ensures, since Dafny refuses that cycle. The dispatch is a lemma axiom instead, and it is sound because the function meets
// the contract of the interface. Without that check the lemma could contradict the contract of next.
function idle_next(q: IdleState, e: Event): Option<State>
  ensures idle_next(q, e).Some? && ValidState(idle_next(q, e).value)
  ensures e == Start ==> phase(idle_next(q, e).value) == Running
  ensures e != Start ==> phase(idle_next(q, e).value) == Idle
{
  if e == Start then Some(RunningAsState(RunningState)) else Some(IdleAsState(IdleState))
}

function running_next(q: RunningState, e: Event): Option<State>
  ensures running_next(q, e).Some? && ValidState(running_next(q, e).value)
  ensures e == Finish ==> phase(running_next(q, e).value) == Done
  ensures e == Reset ==> phase(running_next(q, e).value) == Idle
  ensures e == Start ==> phase(running_next(q, e).value) == Running
{
  if e == Finish then Some(DoneAsState(DoneState))
  else if e == Reset then Some(IdleAsState(IdleState))
  else Some(RunningAsState(RunningState))
}

function done_next(q: DoneState, e: Event): Option<State>
  ensures done_next(q, e).Some? && ValidState(done_next(q, e).value)
  ensures e == Reset ==> phase(done_next(q, e).value) == Idle
  ensures e != Reset ==> phase(done_next(q, e).value) == Done
{
  if e == Reset then Some(IdleAsState(IdleState)) else Some(DoneAsState(DoneState))
}

lemma {:axiom} IdleDispatch(q: IdleState, e: Event)
  ensures next(IdleAsState(q), e) == idle_next(q, e)

lemma {:axiom} RunningDispatch(q: RunningState, e: Event)
  ensures next(RunningAsState(q), e) == running_next(q, e)

lemma {:axiom} DoneDispatch(q: DoneState, e: Event)
  ensures next(DoneAsState(q), e) == done_next(q, e)

datatype Machine = Machine(current_: Option<State>)

predicate ValidMachine(m: Machine) { m.current_.Some? && ValidState(m.current_.value) }

function state(m: Machine): Phase
  requires ValidMachine(m)
{
  phase(m.current_.value)
}

method MakeMachine() returns (m: Machine)
  ensures ValidMachine(m) && state(m) == Idle
{
  m := Machine(Some(IdleAsState(IdleState)));
}

method handle(m: Machine, e: Event) returns (m': Machine)
  requires ValidMachine(m)
  ensures ValidMachine(m')
  ensures e == Reset ==> state(m') == Idle
  ensures state(m) == Idle && e == Start ==> state(m') == Running
  ensures state(m) == Running && e == Finish ==> state(m') == Done
  ensures e != Reset && !(state(m) == Idle && e == Start) && !(state(m) == Running && e == Finish) ==> state(m') == state(m)
{
  m' := Machine(next(m.current_.value, e));
}

method run_to_done() returns (result: Phase)
  ensures result == Done
{
  var m := MakeMachine();
  m := handle(m, Start);
  m := handle(m, Finish);
  result := state(m);
}

method restart() returns (result: Phase)
  ensures result == Running
{
  var m := MakeMachine();
  m := handle(m, Start);
  m := handle(m, Finish);
  m := handle(m, Reset);
  m := handle(m, Start);
  result := state(m);
}
