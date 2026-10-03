class Shape {
public:
  virtual ~Shape() = default;
  virtual int sides() const = 0;
};

class Square : public Shape {
public:
  virtual int sides() const { return 4; }  // BANNED
};
