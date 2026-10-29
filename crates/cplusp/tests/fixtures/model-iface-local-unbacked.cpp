#include <cstdint>

// A local of a final class through a reference to its interface needs a final class over each interface of the file, decision 0217.

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
struct Poker {
  virtual ~Poker() = default;
  //@ requires s.valid()
  //@ modifies s
  //@ ensures s.valid() && s.seen() == 5000
  virtual void poke(Sink& s) const = 0;
};

//@ ensures result == 42
int64_t quiet(const Poker& p) {
  Total t;
  p.poke(t);
  return 0;
}
