#include <cstdint>

// A state machine as a switch over every state, with a switch over every event inside it. The contract is the transition table, one
// line for each rule. The prover follows each path, and the callers prove their final state from the table alone.
enum class State : uint8_t { Idle, Running, Done };
enum class Event : uint8_t { Start, Finish, Reset };

//@ ensures e == Event::Reset ==> result == State::Idle
//@ ensures s == State::Idle && e == Event::Start ==> result == State::Running
//@ ensures s == State::Running && e == Event::Finish ==> result == State::Done
//@ ensures e != Event::Reset && !(s == State::Idle && e == Event::Start) && !(s == State::Running && e == Event::Finish) ==> result == s
State step(State s, Event e) {
  switch (s) {
    case State::Idle:
      switch (e) {
        case Event::Start:
          return State::Running;
        case Event::Finish:
          return State::Idle;
        case Event::Reset:
          return State::Idle;
      }
      break;
    case State::Running:
      switch (e) {
        case Event::Start:
          return State::Running;
        case Event::Finish:
          return State::Done;
        case Event::Reset:
          return State::Idle;
      }
      break;
    case State::Done:
      switch (e) {
        case Event::Start:
          return State::Done;
        case Event::Finish:
          return State::Done;
        case Event::Reset:
          return State::Idle;
      }
      break;
  }
  // No other value arrives here, because the enum_cast row keeps a value that is no enumerator out. The compiler cannot see that,
  // so it needs this return. The model has no such path.
  return s;
}

//@ ensures result == State::Done
State run_to_done() {
  State s = State::Idle;
  s = step(s, Event::Start);
  s = step(s, Event::Finish);
  return s;
}

//@ ensures result == State::Running
State restart() {
  State s = run_to_done();
  s = step(s, Event::Reset);
  s = step(s, Event::Start);
  return s;
}
