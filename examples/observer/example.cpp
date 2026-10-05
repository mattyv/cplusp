#include <cstddef>
#include <cstdint>
#include <memory>
#include <utility>
#include <vector>

// The observer pattern. A subject keeps a list of observers and tells each of them when its value changes. The classic list holds
// pointers to observers that live elsewhere: `std::vector<Observer*>`. The gate does not refuse that member, nor the push_back of
// a pointer parameter, nor a call through `observers_[i]->on_change(v)`. It refuses only a pointer local, such as the loop
// variable of `for (Observer* o : observers_)`, at that line: "Non-owning raw pointer to one object: outside its limit. Limit: A
// parameter only. One object, no ownership, no arithmetic. No pointer member and no pointer local. Use a reference, or a value."
// A vector of pointers is a pointer stored past the call that made it, and the model has no object that dies, so this form is
// not shown here. The subject owns its observers instead, and the list is a vector of unique_ptr. A caller hands an observer over.
// What a caller can then ask is the count of notifications each observer has seen, through the subject.
struct Observer {
  virtual ~Observer() = default;
  // The invariant of each observer, decision 0028. The interface cannot know the fields, so it is virtual.
  virtual bool valid() const = 0;
  // How many notifications the observer has seen.
  //@ requires valid()
  //@ ensures 0 <= result <= 1000
  virtual int32_t seen() const = 0;
  //@ requires valid() && seen() < 1000
  //@ ensures valid() && seen() == old(seen()) + 1
  virtual void on_change(int32_t v) = 0;
};

// An observer that counts.
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

// An observer that counts and keeps the last value.
class Latest final : public Observer {
 public:
  //@ ensures valid() && seen() == 0 && last() == 0
  Latest() : seen_(0), last_(0) {}

  //@ ensures result == (0 <= seen_ && seen_ <= 1000)
  bool valid() const override { return 0 <= seen_ && seen_ <= 1000; }

  //@ requires valid()
  //@ ensures result == seen_
  int32_t seen() const override { return seen_; }

  //@ ensures result == last_
  int32_t last() const { return last_; }

  //@ requires valid() && seen() < 1000
  //@ ensures valid() && seen() == old(seen()) + 1 && last() == v
  void on_change(int32_t v) override {
    last_ = v;
    seen_ += 1;
  }

 private:
  int32_t seen_;
  int32_t last_;
};

class Subject {
 public:
  //@ ensures valid() && observer_count() == 0 && value() == 0
  Subject() : value_(0) {}

  // Every observer is there and valid. The loop is the invariant, written out.
  //@ ensures result == (observers_.size() <= 100 && forall i :: 0 <= i < observers_.size() ==> observers_[i] != nullptr && observers_[i]->valid())
  bool valid() const {
    if (observers_.size() > 100) {
      return false;
    }
    //@ invariant 0 <= i <= observers_.size()
    //@ invariant forall j :: 0 <= j < i ==> observers_[j] != nullptr && observers_[j]->valid()
    for (size_t i = 0; i < observers_.size(); ++i) {
      if (observers_[i] == nullptr || !observers_[i]->valid()) {
        return false;
      }
    }
    return true;
  }

  //@ requires valid()
  //@ ensures result == observers_.size()
  size_t observer_count() const { return observers_.size(); }

  //@ requires valid() && i < observer_count()
  //@ ensures result == observers_[i]->seen()
  int32_t count_of(size_t i) const { return observers_[i]->seen(); }

  //@ ensures result == value_
  int32_t value() const { return value_; }

  // The subject takes the observer over. A new observer has seen nothing, and the others are as they were.
  //@ requires valid() && observer_count() < 100 && o != nullptr && o->valid() && o->seen() == 0
  //@ ensures valid() && observer_count() == old(observer_count()) + 1
  //@ ensures forall i :: 0 <= i < old(observer_count()) ==> count_of(i) == old(count_of(i))
  //@ ensures count_of(old(observer_count())) == 0
  void attach(std::unique_ptr<Observer> o) { observers_.push_back(std::move(o)); }

  // Every observer is told once, so every count goes up by one.
  //@ requires valid() && forall i :: 0 <= i < observer_count() ==> count_of(i) < 1000
  //@ ensures valid() && observer_count() == old(observer_count()) && value() == v
  //@ ensures forall i :: 0 <= i < observer_count() ==> count_of(i) == old(count_of(i)) + 1
  void set(int32_t v) {
    value_ = v;
    //@ invariant 0 <= i <= observers_.size() && observers_.size() == old(observers_.size())
    //@ invariant forall j :: 0 <= j < observers_.size() ==> observers_[j] != nullptr && observers_[j]->valid()
    //@ invariant forall j :: 0 <= j < i ==> count_of(j) == old(count_of(j)) + 1
    //@ invariant forall j :: i <= j < observers_.size() ==> count_of(j) == old(count_of(j)) && count_of(j) < 1000
    for (size_t i = 0; i < observers_.size(); ++i) {
      observers_[i]->on_change(v);
    }
  }

 private:
  std::vector<std::unique_ptr<Observer>> observers_;
  int32_t value_;
};

// Two observers and three changes. Each observer has seen all three.
//@ ensures result == 6
int32_t demo() {
  Subject s;
  s.attach(std::make_unique<Tally>());
  s.attach(std::make_unique<Latest>());
  s.set(10);
  s.set(20);
  s.set(30);
  return s.count_of(0) + s.count_of(1);
}
