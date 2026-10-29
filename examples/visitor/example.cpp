#include <cstddef>
#include <cstdint>
#include <memory>
#include <vector>

// The classic visitor, double dispatch. A shape calls accept(Visitor&), the element class calls back visit(*this) with its own
// type, and the visitor has one visit for each element class. The contracts say what a visit does: it adds the area of the element
// to what the visitor has seen. Then accept says the same in terms of area(), and the driver proves the bound on the total from the
// interface contracts alone. The driver names neither a class of shape nor the class of visitor.
struct Visitor;

struct Shape {
  virtual ~Shape() = default;
  // The invariant of each shape, decision 0028. The interface cannot know the fields, so it is virtual.
  virtual bool valid() const = 0;
  //@ requires valid()
  //@ ensures 0 <= result <= 1000000
  virtual int32_t area() const = 0;
  //@ requires valid() && v.valid() && v.seen() <= 1000000000
  //@ modifies v
  //@ ensures v.valid() && v.seen() == old(v.seen()) + area()
  virtual void accept(Visitor& v) const = 0;
};

class Square final : public Shape {
 public:
  //@ requires 0 <= side <= 1000
  //@ ensures valid() && this->side_ == side
  explicit Square(int32_t side) : side_(side) {}

  //@ ensures result == (0 <= side_ && side_ <= 1000)
  bool valid() const override { return 0 <= side_ && side_ <= 1000; }

  //@ requires valid()
  //@ ensures result == side_ * side_
  //@ ensures 0 <= result <= 1000000
  int32_t area() const override {
    //@ apply MulBound(side_, side_, 1000, 1000)
    return side_ * side_;
  }

  //@ requires valid() && v.valid() && v.seen() <= 1000000000
  //@ modifies v
  //@ ensures v.valid() && v.seen() == old(v.seen()) + area()
  void accept(Visitor& v) const override;

 private:
  int32_t side_;
};

class Rect final : public Shape {
 public:
  //@ requires 0 <= w <= 1000 && 0 <= h <= 1000
  //@ ensures valid() && this->w_ == w && this->h_ == h
  Rect(int32_t w, int32_t h) : w_(w), h_(h) {}

  //@ ensures result == (0 <= w_ && w_ <= 1000 && 0 <= h_ && h_ <= 1000)
  bool valid() const override { return 0 <= w_ && w_ <= 1000 && 0 <= h_ && h_ <= 1000; }

  //@ requires valid()
  //@ ensures result == w_ * h_
  //@ ensures 0 <= result <= 1000000
  int32_t area() const override {
    //@ apply MulBound(w_, h_, 1000, 1000)
    return w_ * h_;
  }

  //@ requires valid() && v.valid() && v.seen() <= 1000000000
  //@ modifies v
  //@ ensures v.valid() && v.seen() == old(v.seen()) + area()
  void accept(Visitor& v) const override;

 private:
  int32_t w_;
  int32_t h_;
};

// The visitor interface. Both classes of shape are complete here, so the contract can name their area.
struct Visitor {
  virtual ~Visitor() = default;
  virtual bool valid() const = 0;
  //@ requires valid()
  //@ ensures result >= 0
  virtual int64_t seen() const = 0;
  //@ requires valid() && s.valid() && seen() <= 1000000000
  //@ ensures valid() && seen() == old(seen()) + s.area()
  virtual void visit(const Square& s) = 0;
  //@ requires valid() && r.valid() && seen() <= 1000000000
  //@ ensures valid() && seen() == old(seen()) + r.area()
  virtual void visit(const Rect& r) = 0;
};

// The second half of each double dispatch. The element names its own type, and the visitor picks the visit for it.
inline void Square::accept(Visitor& v) const {
  v.visit(*this);
}

inline void Rect::accept(Visitor& v) const {
  v.visit(*this);
}

// The concrete visitor. It sums the areas into a member.
class AreaSum final : public Visitor {
 public:
  //@ ensures valid() && seen() == 0
  AreaSum() : total_(0) {}

  //@ ensures result == (0 <= total_ && total_ <= 2000000000)
  bool valid() const override { return 0 <= total_ && total_ <= 2000000000; }

  //@ requires valid()
  //@ ensures result == total_
  int64_t seen() const override { return total_; }

  //@ requires valid() && s.valid() && seen() <= 1000000000
  //@ ensures valid() && seen() == old(seen()) + s.area()
  void visit(const Square& s) override { total_ += s.area(); }

  //@ requires valid() && r.valid() && seen() <= 1000000000
  //@ ensures valid() && seen() == old(seen()) + r.area()
  void visit(const Rect& r) override { total_ += r.area(); }

 private:
  int64_t total_;
};

// The driver. It knows the contracts of Shape and Visitor and nothing else. Every visit adds at most 1000000, and there are at
// most 1000 shapes, so the total stays inside the bound that every visit asks for.
//@ requires shapes.size() <= 1000
//@ requires forall i :: 0 <= i < shapes.size() ==> shapes[i] != nullptr
//@ requires forall i :: 0 <= i < shapes.size() ==> shapes[i]->valid()
//@ requires v.valid() && v.seen() == 0
//@ modifies v
//@ ensures v.valid() && 0 <= v.seen() <= 1000000 * shapes.size()
void visit_all(const std::vector<std::unique_ptr<Shape>>& shapes, Visitor& v) {
  //@ invariant 0 <= i <= shapes.size()
  //@ invariant v.valid() && 0 <= v.seen() <= 1000000 * i
  for (size_t i = 0; i < shapes.size(); ++i) {
    shapes[i]->accept(v);
  }
}

//@ requires shapes.size() <= 1000
//@ requires forall i :: 0 <= i < shapes.size() ==> shapes[i] != nullptr
//@ requires forall i :: 0 <= i < shapes.size() ==> shapes[i]->valid()
//@ ensures 0 <= result <= 1000000000
int64_t total_area(const std::vector<std::unique_ptr<Shape>>& shapes) {
  AreaSum sum;
  visit_all(shapes, sum);
  return sum.seen();
}

//@ ensures 0 <= result <= 1000000000
int64_t sample_total() {
  std::vector<std::unique_ptr<Shape>> shapes;
  shapes.push_back(std::make_unique<Square>(5));
  shapes.push_back(std::make_unique<Rect>(2, 3));
  return total_area(shapes);
}
