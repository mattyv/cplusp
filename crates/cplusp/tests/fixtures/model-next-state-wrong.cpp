#include <cstdint>
#include <memory>

// Claims about a state that gives the next state that do not hold, decision 0199.
enum class Light : uint8_t { Red, Green };

struct Signal {
  virtual ~Signal() = default;
  virtual Light light() const = 0;
  //@ ensures result != nullptr
  //@ ensures !go ==> result->light() == Light::Red
  virtual std::unique_ptr<Signal> next(bool go) const = 0;
};

// Gives green also when go is false, so it breaks the promise of the interface.
class GreenSignal final : public Signal {
 public:
  //@ ensures result == Light::Green
  Light light() const override { return Light::Green; }

  //@ ensures result != nullptr
  std::unique_ptr<Signal> next(bool go) const override {
    if (go) {
      return std::make_unique<GreenSignal>();
    }
    return std::make_unique<GreenSignal>();
  }
};

struct Level {
  int32_t v;

  //@ ensures result == v
  int32_t clamped() const {
    if (v < 0) {
      return 0;
    }
    return v;
  }
};
