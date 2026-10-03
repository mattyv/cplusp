#include <cstdint>
class Drawable {
public:
  virtual ~Drawable() = default;
  virtual int32_t draw() const = 0;
};

class Named {
public:
  virtual ~Named() = default;
  virtual int32_t name_length() const = 0;
};

class Widget {
public:
  int32_t id() const { return id_; }

private:
  int32_t id_ = 7;
};

// One concrete base. Every other base is a pure interface.
class Button : public Widget, public Drawable, public Named {
public:
  int32_t draw() const override { return id(); }
  int32_t name_length() const override { return 6; }
};
