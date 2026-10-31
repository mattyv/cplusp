#include <cstdint>
#include <memory>
#include <utility>

// A function that ends the life of no object has no edge to a destructor, so a destructor can call through an interface, decision 0222.

struct Log {
  virtual ~Log() = default;
  virtual bool valid() const = 0;
  //@ requires valid()
  //@ ensures true
  virtual void note() const = 0;
};

class Quiet final : public Log {
 public:
  //@ ensures result == true
  bool valid() const override { return true; }
  //@ requires valid()
  //@ ensures true
  void note() const override {}
};

struct Guard {
  std::unique_ptr<Log> log_;
  //@ requires log_ != nullptr && log_->valid()
  //@ ensures true
  ~Guard() { log_->note(); }
};
