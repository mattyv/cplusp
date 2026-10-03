class Counter {
public:
  int value() const { return value_; }
  void add(int n) { value_ += n; }

private:
  int value_ = 0;
};
