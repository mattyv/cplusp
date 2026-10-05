#include <cstdint>
#include <memory>

// The state pattern with objects. Each state is a class, and an event goes to the state object, which answers with the next state
// object. The context owns the current state and forwards events to it. The table of transitions is the contract of next(), written
// with phase(), which says which state an object is. Compare the folder state_machine, where the states are an enum and the table
// is a switch. Here a caller proves the state after a fixed sequence from the contract of the context alone.
enum class Phase : uint8_t { Idle, Running, Done };
enum class Event : uint8_t { Start, Finish, Reset };

struct State {
  virtual ~State() = default;
  // The invariant of each state, decision 0028. The interface cannot know the fields, so it is virtual.
  virtual bool valid() const = 0;
  //@ requires valid()
  virtual Phase phase() const = 0;
  //@ requires valid()
  //@ ensures result != nullptr && result->valid()
  //@ ensures e == Event::Reset ==> result->phase() == Phase::Idle
  //@ ensures phase() == Phase::Idle && e == Event::Start ==> result->phase() == Phase::Running
  //@ ensures phase() == Phase::Running && e == Event::Finish ==> result->phase() == Phase::Done
  //@ ensures e != Event::Reset && !(phase() == Phase::Idle && e == Event::Start) && !(phase() == Phase::Running && e == Event::Finish) ==> result->phase() == phase()
  virtual std::unique_ptr<State> next(Event e) const = 0;
};

class IdleState final : public State {
 public:
  //@ ensures result == true
  bool valid() const override { return true; }

  //@ ensures result == Phase::Idle
  Phase phase() const override { return Phase::Idle; }

  //@ requires valid()
  //@ ensures result != nullptr && result->valid()
  //@ ensures e == Event::Start ==> result->phase() == Phase::Running
  //@ ensures e != Event::Start ==> result->phase() == Phase::Idle
  std::unique_ptr<State> next(Event e) const override;
};

class RunningState final : public State {
 public:
  //@ ensures result == true
  bool valid() const override { return true; }

  //@ ensures result == Phase::Running
  Phase phase() const override { return Phase::Running; }

  //@ requires valid()
  //@ ensures result != nullptr && result->valid()
  //@ ensures e == Event::Finish ==> result->phase() == Phase::Done
  //@ ensures e == Event::Reset ==> result->phase() == Phase::Idle
  //@ ensures e == Event::Start ==> result->phase() == Phase::Running
  std::unique_ptr<State> next(Event e) const override;
};

class DoneState final : public State {
 public:
  //@ ensures result == true
  bool valid() const override { return true; }

  //@ ensures result == Phase::Done
  Phase phase() const override { return Phase::Done; }

  //@ requires valid()
  //@ ensures result != nullptr && result->valid()
  //@ ensures e == Event::Reset ==> result->phase() == Phase::Idle
  //@ ensures e != Event::Reset ==> result->phase() == Phase::Done
  std::unique_ptr<State> next(Event e) const override;
};

// Each state names the others, so the bodies come after all three classes.
inline std::unique_ptr<State> IdleState::next(Event e) const {
  if (e == Event::Start) {
    return std::make_unique<RunningState>();
  }
  return std::make_unique<IdleState>();
}

inline std::unique_ptr<State> RunningState::next(Event e) const {
  if (e == Event::Finish) {
    return std::make_unique<DoneState>();
  }
  if (e == Event::Reset) {
    return std::make_unique<IdleState>();
  }
  return std::make_unique<RunningState>();
}

inline std::unique_ptr<State> DoneState::next(Event e) const {
  if (e == Event::Reset) {
    return std::make_unique<IdleState>();
  }
  return std::make_unique<DoneState>();
}

// The context. It owns the current state, and it never names a class of state but the first.
class Machine {
 public:
  //@ ensures valid() && state() == Phase::Idle
  Machine() : current_(std::make_unique<IdleState>()) {}

  //@ ensures result == (current_ != nullptr && current_->valid())
  bool valid() const { return current_ != nullptr && current_->valid(); }

  //@ requires valid()
  //@ ensures result == current_->phase()
  Phase state() const { return current_->phase(); }

  //@ requires valid()
  //@ ensures valid()
  //@ ensures e == Event::Reset ==> state() == Phase::Idle
  //@ ensures old(state()) == Phase::Idle && e == Event::Start ==> state() == Phase::Running
  //@ ensures old(state()) == Phase::Running && e == Event::Finish ==> state() == Phase::Done
  //@ ensures e != Event::Reset && !(old(state()) == Phase::Idle && e == Event::Start) && !(old(state()) == Phase::Running && e == Event::Finish) ==> state() == old(state())
  void handle(Event e) { current_ = current_->next(e); }

 private:
  std::unique_ptr<State> current_;
};

//@ ensures result == Phase::Done
Phase run_to_done() {
  Machine m;
  m.handle(Event::Start);
  m.handle(Event::Finish);
  return m.state();
}

//@ ensures result == Phase::Running
Phase restart() {
  Machine m;
  m.handle(Event::Start);
  m.handle(Event::Finish);
  m.handle(Event::Reset);
  m.handle(Event::Start);
  return m.state();
}
