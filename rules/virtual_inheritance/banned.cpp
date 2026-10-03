class Base {
public:
  int id() const { return 1; }
};

class Derived : public virtual Base {};  // BANNED

int id_of(const Derived& d) {
  return d.id();
}
