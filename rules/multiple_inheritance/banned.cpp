#include <cstdint>
class Engine {
public:
  int32_t power() const { return power_; }

private:
  int32_t power_ = 100;
};

class Wheels {
public:
  int32_t count() const { return count_; }

private:
  int32_t count_ = 4;
};

class Car : public Engine, public Wheels {  // BANNED
public:
  int32_t total() const { return power() + count(); }
};

// An interface that carries data is not an interface.
class Logger {
public:
  virtual ~Logger() = default;
  virtual int32_t log() const = 0;
  int32_t level = 0;
};

class Loud : public Engine, public Logger {  // BANNED
public:
  int32_t log() const override { return level + power(); }
};

// A template is judged at each instantiation, decision 0055. Both bases are concrete in Both<Left, Right>.
struct Left {
  int32_t l = 0;
};
struct Right {
  int32_t r = 0;
};
template <class X, class Y>
struct Both : X, Y {};  // BANNED

int32_t both() {
  Both<Left, Right> lr;
  return lr.l + lr.r;
}
