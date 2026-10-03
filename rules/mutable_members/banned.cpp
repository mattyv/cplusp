class Cache {
public:
  int get() const {
    hits_ += 1;
    return value_;
  }

private:
  int value_ = 0;
  mutable int hits_ = 0;  // BANNED
};
