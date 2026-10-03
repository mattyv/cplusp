class Engine {
public:
  int power() const { return power_; }

private:
  int power_ = 100;
};

class Wheels {
public:
  int count() const { return count_; }

private:
  int count_ = 4;
};

class Car : public Engine, public Wheels {  // BANNED
public:
  int total() const { return power() + count(); }
};

// An interface that carries data is not an interface.
class Logger {
public:
  virtual ~Logger() = default;
  virtual int log() const = 0;
  int level = 0;
};

class Loud : public Engine, public Logger {  // BANNED
public:
  int log() const override { return level + power(); }
};
