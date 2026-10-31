#include <cstdint>
#include <memory>
#include <utility>
#include <vector>

struct Log {
  virtual ~Log() = default;
  virtual bool valid() const = 0;
  //@ requires valid()
  //@ ensures true
  virtual void note() const = 0;
};

struct Guard {
  std::unique_ptr<Log> log_;
  //@ requires l != nullptr && l->valid()
  //@ ensures log_ != nullptr && log_->valid()
  explicit Guard(std::unique_ptr<Log> l) : log_(std::move(l)) {}
  //@ requires log_ != nullptr && log_->valid()
  //@ ensures true
  ~Guard() { log_->note(); }
};

class Loud final : public Log {
 public:
  //@ ensures result == true
  bool valid() const override { return true; }
  //@ requires valid()
  //@ ensures true
  void note() const override;
};

//@ ensures result != nullptr && result->valid()
std::unique_ptr<Log> make_loud() {
  return std::make_unique<Loud>();
}

//@ requires p != nullptr
//@ ensures true
void take(std::unique_ptr<Log> p) {}

void Loud::note() const {
  take(make_loud());
}
