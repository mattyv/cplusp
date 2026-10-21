#include <cstddef>
#include <cstdint>
#include <memory>
#include <vector>

// The forms of a vector of unique_ptr that have no rule yet, decision 0170.
struct Observer {
  virtual ~Observer() = default;
  virtual bool valid() const = 0;
  //@ requires valid()
  //@ ensures 0 <= result && result <= 1000
  virtual int32_t seen() const = 0;
  //@ requires valid() && seen() < 1000
  //@ ensures valid() && seen() == old(seen()) + 1
  virtual void on_change(int32_t v) = 0;
};

class Tally final : public Observer {
 public:
  //@ ensures valid() && seen() == 0
  Tally() : seen_(0) {}
  //@ ensures result == (0 <= seen_ && seen_ <= 1000)
  bool valid() const override { return 0 <= seen_ && seen_ <= 1000; }
  //@ requires valid()
  //@ ensures result == seen_
  int32_t seen() const override { return seen_; }
  //@ requires valid() && seen() < 1000
  //@ ensures valid() && seen() == old(seen()) + 1
  void on_change(int32_t) override { seen_ += 1; }

 private:
  int32_t seen_;
};

//@ modifies o
//@ requires o.valid() && o.seen() < 999
//@ ensures o.valid() && o.seen() == old(o.seen()) + 2
void ping(Observer& o) {
  o.on_change(1);
  o.on_change(2);
}


int32_t assign() {
  std::vector<std::unique_ptr<Observer>> v;
  v.push_back(std::make_unique<Tally>());
  v[0] = std::make_unique<Tally>();
  return 0;
}

//@ requires v.size() <= 10
int32_t count(const std::vector<std::unique_ptr<Observer>>& v) {
  int32_t n = 0;
  for (const std::unique_ptr<Observer>& p : v) {
    n += 1;
  }
  return n;
}

//@ modifies v
//@ requires v.size() == 1 && v[0] != nullptr && v[0]->valid() && v[0]->seen() < 999
void deref(std::vector<std::unique_ptr<Observer>>& v) {
  ping(*v[0]);
}

std::vector<std::unique_ptr<Observer>> make() {
  std::vector<std::unique_ptr<Observer>> v;
  return v;
}

struct Bumper {
  virtual ~Bumper() = default;
  //@ modifies k
  //@ ensures k == old(k) + 1
  virtual void bump(size_t& k) = 0;
};

//@ modifies v
//@ requires v.size() == 2 && v[0] != nullptr && v[1] != nullptr
void hazard(std::vector<std::unique_ptr<Bumper>>& v) {
  size_t k = 0;
  v[k]->bump(k);
}
