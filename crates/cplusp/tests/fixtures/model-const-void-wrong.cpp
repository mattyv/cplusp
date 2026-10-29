#include <cstdint>

// A const virtual function that gives no value and writes a reference parameter, decision 0209. An override that breaks the promise fails its check.

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

struct Source {
  virtual ~Source() = default;
  //@ requires s.valid() && s.seen() <= 1000
  //@ modifies s
  //@ ensures s.valid() && s.seen() == old(s.seen()) + 2
  virtual void give(Sink& s) const = 0;
};

class Two final : public Source {
 public:
  //@ requires s.valid() && s.seen() <= 1000
  //@ modifies s
  //@ ensures s.valid() && s.seen() == old(s.seen()) + 3
  void give(Sink& s) const override { s.add(3); }
};

//@ requires s.valid() && s.seen() <= 1000
//@ modifies s
//@ ensures s.valid() && s.seen() == old(s.seen()) + 2
void use(const Source& src, Sink& s) {
  src.give(s);
}
