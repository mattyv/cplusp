#include <cstdint>

// An enum class is a datatype, and a switch over it is a match, decision 0109.
enum class Kind : uint8_t { Small, Large };
enum class State : uint8_t { Idle, Running, Done };
enum class Event : uint8_t { Start, Finish, Reset };
enum class Error : uint8_t { None, Negative, TooBig };

struct Result {
  bool ok;
  Error error;
  int32_t value;
};

//@ ensures result == (k == Kind::Small ? 1 : 10)
int32_t weight(Kind k) {
  switch (k) {
    case Kind::Small:
      return 1;
    case Kind::Large:
      return 10;
  }
  return 0;
}

//@ ensures e == Event::Reset ==> result == State::Idle
//@ ensures s == State::Idle && e == Event::Start ==> result == State::Running
//@ ensures s == State::Running && e == Event::Finish ==> result == State::Done
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
      if (e == Event::Reset) {
        return State::Idle;
      }
      break;
  }
  return s;
}

//@ ensures result == State::Done
State run_to_done() {
  State s = State::Idle;
  s = step(s, Event::Start);
  s = step(s, Event::Finish);
  return s;
}

//@ ensures x < 0 ==> !result.ok && result.error == Error::Negative
//@ ensures 0 <= x && x <= 46340 ==> result.ok && result.value == x * x
Result checked_square(int32_t x) {
  if (x < 0) {
    return Result{false, Error::Negative, 0};
  }
  if (x > 46340) {
    return Result{false, Error::TooBig, 0};
  }
  return Result{true, Error::None, x * x};
}

//@ ensures x < 0 ==> result == -1
//@ ensures 0 <= x && x <= 46340 ==> result == x * x
int32_t square_or_code(int32_t x) {
  Result r = checked_square(x);
  int32_t code = 0;
  switch (r.error) {
    case Error::None:
      code = r.value;
      break;
    case Error::Negative:
      code = -1;
      break;
    case Error::TooBig:
      code = -2;
      break;
  }
  return code;
}
