#include <cstdint>
class Engine {
public:
  int32_t power() const { return 100; }
};

class Car {
public:
  int32_t power() const { return engine_.power(); }

private:
  Engine engine_;
};
