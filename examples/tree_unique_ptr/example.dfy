// A unique_ptr<Node> is an Option of Node, decision 0029, and the tree is the Option folded into one recursive datatype. Nil is the null
// pointer and Node is an owned node with its two children. Size, Sum and Within are the specification functions the contracts name. The
// method sum carries `decreases Size(root)`, and Dafny proves that each child is smaller. The lemma gives the bound on a sum from the
// bound on the values: every value is at most 10^6 in magnitude and there are at most 10^3 nodes, so every partial sum is inside int32.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Tree = Nil | Node(value: int32, left: Tree, right: Tree)

function Size(t: Tree): nat
  decreases t
{
  match t
    case Nil => 0
    case Node(_, l, r) => 1 + Size(l) + Size(r)
}

function Sum(t: Tree): int
  decreases t
{
  match t
    case Nil => 0
    case Node(v, l, r) => v as int + Sum(l) + Sum(r)
}

predicate Within(t: Tree, bound: int)
  decreases t
{
  match t
    case Nil => true
    case Node(v, l, r) => -bound <= v as int <= bound && Within(l, bound) && Within(r, bound)
}

lemma SumBound(t: Tree)
  requires Within(t, 1_000_000)
  ensures -1_000_000 * Size(t) <= Sum(t) <= 1_000_000 * Size(t)
  decreases t
{
  match t
    case Nil =>
    case Node(_, l, r) =>
      SumBound(l);
      SumBound(r);
}

method sum(root: Tree) returns (result: int32)
  requires Size(root) <= 1000 && Within(root, 1_000_000)
  decreases Size(root)
  ensures result as int == Sum(root)
{
  if root.Nil? {
    return 0;
  }
  SumBound(root.left);
  SumBound(root.right);
  var from_left := sum(root.left);
  var from_right := sum(root.right);
  return root.value + from_left + from_right;
}

method leaf(value: int32) returns (result: Tree)
  requires -1_000_000 <= value as int <= 1_000_000
  ensures result.Node? && Size(result) == 1 && Sum(result) == value as int && Within(result, 1_000_000)
{
  var n := Node(0, Nil, Nil);
  n := n.(value := value);
  return n;
}

method parent(value: int32, left: Tree, right: Tree) returns (result: Tree)
  requires -1_000_000 <= value as int <= 1_000_000 && Within(left, 1_000_000) && Within(right, 1_000_000)
  ensures result.Node? && Size(result) == 1 + Size(left) + Size(right) && Sum(result) == value as int + Sum(left) + Sum(right)
  ensures Within(result, 1_000_000)
{
  var n := Node(0, Nil, Nil);
  n := n.(value := value);
  n := n.(left := left);
  n := n.(right := right);
  return n;
}

method sum_of_three() returns (result: int32)
  ensures result == 6
{
  var a := leaf(1);
  var b := leaf(3);
  var t := parent(2, a, b);
  result := sum(t);
}
