#include "../../../../include/cplusp.h"
#include <cstdint>

// A trusted body can call each function of the file, so the call of the interface in it can come back, decision 0223.

struct Sink {
  virtual ~Sink() = default;
  virtual bool valid() const = 0;
  //@ requires valid()
  //@ ensures result >= 0
  virtual int64_t seen() const = 0;
  //@ requires valid() && seen() <= 1000 && 0 <= k <= 10
  //@ ensures valid() && seen() == old(seen()) + k
  virtual void add(int32_t k) = 0;
};

class Total final : public Sink {
 public:
  //@ ensures valid() && seen() == 0
  Total() : total_(0) {}
  //@ ensures result == (0 <= total_ && total_ <= 2000)
  bool valid() const override { return 0 <= total_ && total_ <= 2000; }
  //@ requires valid()
  //@ ensures result == total_
  int64_t seen() const override { return total_; }
  //@ requires valid() && seen() <= 1000 && 0 <= k <= 10
  //@ ensures valid() && seen() == old(seen()) + k
  void add(int32_t k) override { total_ += k; }
 private:
  int64_t total_;
};
struct Filler {
  virtual ~Filler() = default;
  //@ requires s.valid()
  //@ modifies s
  //@ ensures s.valid() && s.seen() == 1 && s.seen() == 2
  virtual void fill(Sink& s) const = 0;
};

class Loop final : public Filler {
 public:
  //@ requires s.valid()
  //@ modifies s
  //@ ensures s.valid() && s.seen() == 1 && s.seen() == 2
  void fill(Sink& s) const override;
};

CPLUSP_TRUSTED("fills elsewhere")
//@ requires s.valid()
//@ modifies s
//@ ensures s.valid() && s.seen() == 1 && s.seen() == 2
void helper(const Filler& f, Sink& s) {
  f.fill(s);
}

void Loop::fill(Sink& s) const {
  helper(*this, s);
}

//@ requires s.valid()
//@ modifies s
//@ ensures result == 42
int64_t quiet(const Filler& f, Sink& s) {
  f.fill(s);
  return 0;
}
