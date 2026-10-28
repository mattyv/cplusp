#include <cstdint>
#include <memory>

// A state that gives the next state, decision 0199.
enum class Light : uint8_t { Red, Green };

struct Signal {
  virtual ~Signal() = default;
  virtual Light light() const = 0;
  //@ ensures result != nullptr
  //@ ensures go ==> result->light() == Light::Green
  //@ ensures !go ==> result->light() == Light::Red
  virtual std::unique_ptr<Signal> next(bool go) const = 0;
};

class RedSignal final : public Signal {
 public:
  //@ ensures result == Light::Red
  Light light() const override { return Light::Red; }

  //@ ensures result != nullptr
  //@ ensures go ==> result->light() == Light::Green
  //@ ensures !go ==> result->light() == Light::Red
  std::unique_ptr<Signal> next(bool go) const override;
};

class GreenSignal final : public Signal {
 public:
  //@ ensures result == Light::Green
  Light light() const override { return Light::Green; }

  //@ ensures result != nullptr
  //@ ensures go ==> result->light() == Light::Green
  //@ ensures !go ==> result->light() == Light::Red
  std::unique_ptr<Signal> next(bool go) const override;
};

inline std::unique_ptr<Signal> RedSignal::next(bool go) const {
  if (go) {
    return std::make_unique<GreenSignal>();
  }
  return std::make_unique<RedSignal>();
}

inline std::unique_ptr<Signal> GreenSignal::next(bool go) const {
  if (!go) {
    return std::make_unique<RedSignal>();
  } else {
    return std::make_unique<GreenSignal>();
  }
}

// The context knows only the interface.
class Crossing {
 public:
  //@ ensures has() && shows() == Light::Red
  Crossing() : now_(std::make_unique<RedSignal>()) {}

  //@ ensures result == (now_ != nullptr)
  bool has() const { return now_ != nullptr; }

  //@ requires has()
  //@ ensures result == now_->light()
  Light shows() const { return now_->light(); }

  //@ requires has()
  //@ ensures has() && (go ==> shows() == Light::Green) && (!go ==> shows() == Light::Red)
  void step(bool go) { now_ = now_->next(go); }

 private:
  std::unique_ptr<Signal> now_;
};

//@ ensures result == Light::Green
Light walk() {
  Crossing c;
  c.step(false);
  c.step(true);
  return c.shows();
}

// A pure member function with an early return, which a contract calls.
struct Level {
  int32_t v;

  //@ ensures result == (v < 0 ? 0 : (v > 9 ? 9 : v))
  int32_t clamped() const {
    if (v < 0) {
      return 0;
    }
    if (v > 9) {
      return 9;
    }
    return v;
  }

  //@ ensures result == (clamped() <= 9)
  bool low() const { return clamped() <= 9; }
};
