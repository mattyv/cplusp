class Engine {
public:
  int power() const { return 100; }
};

class Car {
public:
  int power() const { return engine_.power(); }

private:
  Engine engine_;
};
