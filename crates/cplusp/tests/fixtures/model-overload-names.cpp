#include <cstdint>

// A name of two virtual functions stays plain in each sentence, and a contract that calls it is no pure function, decisions 0210 and 0217.

struct Late {
  virtual ~Late() = default;
  //@ requires ready()
  //@ ensures result >= 0
  virtual int32_t apply(int32_t k) const = 0;
  //@ ensures result >= 0
  virtual int32_t apply(bool b) const = 0;
  virtual bool ready() const = 0;
};

class Soon final : public Late {
 public:
  //@ requires ready()
  //@ ensures result >= 0
  int32_t apply(int32_t k) const override { return 0; }
  //@ ensures result >= 0
  int32_t apply(bool b) const override { return 0; }
  bool ready() const override { return true; }
};

struct Self {
  virtual ~Self() = default;
  //@ ensures result >= 0
  virtual int32_t size(int32_t k) const = 0;
  //@ ensures result == size(true)
  virtual int32_t size(bool b) const = 0;
};
