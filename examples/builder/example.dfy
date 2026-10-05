// A builder is a datatype, decision 0029, and each step is a method that takes it in and gives it back. A step returns the builder
// itself, which the C++ contract says with `&result == this`, so the chain is one object changed three times. The model hoists the
// calls in the order C++ gives them: the object of each call first, and the inner call before the outer one.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Config = Config(width: int32, height: int32, depth: int32)

datatype Builder = Builder(width: int32, height: int32, depth: int32)

predicate Valid(b: Builder) { 0 <= b.width <= 1000 && 0 <= b.height <= 1000 && 0 <= b.depth <= 1000 }

method MakeBuilder() returns (b: Builder)
  ensures Valid(b) && b.width == 0 && b.height == 0 && b.depth == 0
{
  b := Builder(0, 0, 0);
}

method set_width(b: Builder, w: int32) returns (b': Builder)
  requires Valid(b) && 0 <= w <= 1000
  ensures Valid(b') && b'.width == w && b'.height == b.height && b'.depth == b.depth
{
  b' := b.(width := w);
}

method set_height(b: Builder, h: int32) returns (b': Builder)
  requires Valid(b) && 0 <= h <= 1000
  ensures Valid(b') && b'.height == h && b'.width == b.width && b'.depth == b.depth
{
  b' := b.(height := h);
}

method set_depth(b: Builder, d: int32) returns (b': Builder)
  requires Valid(b) && 0 <= d <= 1000
  ensures Valid(b') && b'.depth == d && b'.width == b.width && b'.height == b.height
{
  b' := b.(depth := d);
}

function build(b: Builder): Config
  requires Valid(b)
  ensures build(b).width == b.width && build(b).height == b.height && build(b).depth == b.depth
{
  Config(b.width, b.height, b.depth)
}

method make_box() returns (result: Config)
  ensures result.width == 10 && result.height == 20 && result.depth == 30
{
  var b := MakeBuilder();
  b := set_width(b, 10);
  b := set_height(b, 20);
  b := set_depth(b, 30);
  result := build(b);
}

method make_flat() returns (result: Config)
  ensures result.width == 7 && result.height == 0 && result.depth == 9
{
  var b := MakeBuilder();
  b := set_depth(b, 9);
  b := set_width(b, 7);
  result := build(b);
}
