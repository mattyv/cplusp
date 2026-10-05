// An enum class is a datatype of its enumerators. The switch is a match, and a match must cover every enumerator, as the C++ switch
// does. The function step is pure, so it is a Dafny function, and its contract is the same table. The callers are methods that hoist
// each call into a statement.
datatype State = Idle | Running | Done
datatype Event = Start | Finish | Reset

function step(s: State, e: Event): State
  ensures e == Reset ==> step(s, e) == Idle
  ensures s == Idle && e == Start ==> step(s, e) == Running
  ensures s == Running && e == Finish ==> step(s, e) == Done
  ensures e != Reset && !(s == Idle && e == Start) && !(s == Running && e == Finish) ==> step(s, e) == s
{
  match s {
    case Idle =>
      match e {
        case Start => Running
        case Finish => Idle
        case Reset => Idle
      }
    case Running =>
      match e {
        case Start => Running
        case Finish => Done
        case Reset => Idle
      }
    case Done =>
      match e {
        case Start => Done
        case Finish => Done
        case Reset => Idle
      }
  }
}

method run_to_done() returns (result: State)
  ensures result == Done
{
  var s := Idle;
  s := step(s, Start);
  s := step(s, Finish);
  result := s;
}

method restart() returns (result: State)
  ensures result == Running
{
  var s := run_to_done();
  s := step(s, Reset);
  s := step(s, Start);
  result := s;
}
