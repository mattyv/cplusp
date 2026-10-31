#include "../../../../include/cplusp.h"
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

CPLUSP_TRUSTED("logs elsewhere")
//@ ensures true
void spawn() {
  Guard g(std::make_unique<Loud>());
}

void Loud::note() const {
  spawn();
}
