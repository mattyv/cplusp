#include <cstdint>
class Base {
public:
  int32_t id() const { return 1; }
};

class Derived : public virtual Base {};  // BANNED

int32_t id_of(const Derived& d) {
  return d.id();
}
