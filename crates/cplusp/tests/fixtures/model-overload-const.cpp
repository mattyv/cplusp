#include <cstdint>

// A const and a non-const virtual function of one name are two overloads, decision 0217.

struct Look {
  virtual ~Look() = default;
  //@ ensures result == 1
  virtual int32_t see() const = 0;
  //@ ensures result == 2
  virtual int32_t see() = 0;
};

class Eye final : public Look {
 public:
  //@ ensures result == 1
  int32_t see() const override { return 1; }
  //@ ensures result == 5
  int32_t see() override { return 5; }
};

//@ modifies l
//@ ensures result == 2
int32_t peek(Look& l) {
  return l.see();
}

//@ ensures result == 1
int32_t peekc(const Look& l) {
  return l.see();
}
