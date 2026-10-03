class Drawable {
public:
  virtual ~Drawable() = default;
  virtual int draw() const = 0;
};

class Named {
public:
  virtual ~Named() = default;
  virtual int name_length() const = 0;
};

class Widget {
public:
  int id() const { return id_; }

private:
  int id_ = 7;
};

// One concrete base. Every other base is a pure interface.
class Button : public Widget, public Drawable, public Named {
public:
  int draw() const override { return id(); }
  int name_length() const override { return 6; }
};
