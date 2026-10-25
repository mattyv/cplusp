#include <cstdint>
#include <map>
#include <vector>

// The forms of a class template that have no rule yet, decision 0188.

// A class template with no instance.
template <typename T>
struct Unused {
  T v;
};

// A type argument with no Dafny name.
template <typename T>
struct Holder {
  T v;
};

//@ ensures true
int32_t held(const Holder<std::vector<int32_t>>& h) {
  return 0;
}

// A member function template.
template <typename T>
class Conv {
 public:
  //@ ensures result == v_
  T get() const { return v_; }

  //@ ensures true
  template <typename U>
  U as(U u) const {
    return u;
  }

 private:
  T v_;
};

template class Conv<int32_t>;

// A member function that only a contract calls has no body without an explicit instantiation.
template <typename T>
class Gauge {
 public:
  //@ ensures result == (v_ >= 0)
  bool valid() const { return v_ >= 0; }

  //@ requires valid()
  //@ ensures result == v_
  T get() const { return v_; }

 private:
  T v_;
};

//@ requires g.valid()
//@ ensures result == g.get()
int32_t read(const Gauge<int32_t>& g) {
  return g.get();
}

// A contract that calls valid() through a field, or through a reference parameter, names the member with no body.
struct Wrap {
  Gauge<int32_t> g;
};

//@ requires w.g.valid()
//@ ensures result == w.g.get()
int32_t through_field(const Wrap& w) {
  return w.g.get();
}

//@ modifies g
//@ requires g.valid()
//@ ensures result == g.get()
int32_t through_ref(Gauge<int32_t>& g) {
  return g.get();
}

// A member that writes is no pure function, beside an instance.
struct Other {
  int32_t n = 0;
  bool valid() {
    n = 1;
    return true;
  }
};

//@ requires o.valid()
//@ ensures result == g.get()
int32_t beside(const Gauge<int32_t>& g, Other o) {
  return g.get();
}

// An instance that is no struct of the model keeps the refusal of its members: a dependent base, and a map field.
template <typename T>
struct Base {
  T v;
};

template <typename T>
struct Der : Base<T> {
  //@ ensures result == 0
  T get() const { return this->v; }
};

template struct Der<int32_t>;

template <typename T>
struct Keyed {
  std::map<T, T> m;
  //@ ensures result == 0
  int32_t get() const { return 1; }
};

template struct Keyed<int32_t>;

// A member function with a contract whose body no instance makes.
template <typename T>
struct Cell {
  T v;
  //@ ensures result == v + 1
  T get() const { return v; }
};

//@ ensures result == 1
int32_t cell() {
  const Cell<int32_t> c{1};
  return c.v;
}

// A class template that only a declaration names has no instance.
template <typename T>
struct Named {
  T v;
  //@ ensures result == v + 1
  T get() const { return v; }
};

int32_t named(Named<int32_t>* p);

// A contract that reads value() or calls operator() of an instance that makes neither.
template <typename T>
struct Meter {
  T v;
  //@ ensures result == v
  T value() const { return v; }
  //@ ensures result == v + x
  T operator()(T x) const { return v + x; }
};

//@ requires m.v < 10 && m.v > 0
//@ ensures result == m.value()
int32_t meter_value(const Meter<int32_t>& m) {
  return m.v;
}

//@ requires m.v < 10 && m.v > 0
//@ ensures result == m(1)
int32_t meter_call(const Meter<int32_t>& m) {
  return m.v + 1;
}

// A const member function of a plain struct that the file only declares has no model.
struct Probe {
  int32_t v = 0;
  bool valid() const;
};

//@ requires p.valid()
//@ ensures result == p.v
int32_t probe(const Probe& p) {
  return p.v;
}
