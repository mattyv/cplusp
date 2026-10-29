#include <cstdint>

// A contract of an interface that reads a later function or itself, and a pure virtual function with no value, decision 0166.
struct Late {
  virtual ~Late() = default;
  //@ requires ready()
  virtual int32_t apply() const = 0;
  virtual bool ready() const = 0;
};

class Soon final : public Late {
 public:
  //@ requires ready()
  int32_t apply() const override { return 1; }
  bool ready() const override { return true; }
};

// A const pure virtual function that gives no value is a method, decision 0209.
struct Quiet {
  virtual ~Quiet() = default;
  virtual void drop() const = 0;
};

struct Loop {
  virtual ~Loop() = default;
  //@ ensures result == size()
  virtual int32_t size() const = 0;
};
