class Meters {
public:
  Meters(int v) : value_(v) {}  // BANNED
  operator int() const { return value_; }  // BANNED

private:
  int value_;
};

int twice(const Meters& m) {
  return m * 2;
}
