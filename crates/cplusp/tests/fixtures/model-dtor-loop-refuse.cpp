#include <cstdint>
#include <memory>
#include <utility>

// A local whose destructor calls back through the interface ends a life, so the call in the destructor can come back, decision 0222.
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

void Loud::note() const {
  Guard g(std::make_unique<Loud>());
}
