class Meters {
public:
  explicit Meters(int v) : value_(v) {}
  explicit operator int() const { return value_; }

private:
  int value_;
};

int twice(const Meters& m) {
  return static_cast<int>(m) * 2;
}
