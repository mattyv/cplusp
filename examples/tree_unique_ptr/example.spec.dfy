// The tree of the model is an Option of S_Node, decision 0029. None is the null pointer. Size, Sum and Within fold the tree. Each
// recursion goes to a child, and a child is a part of its parent, so Dafny proves that each one ends.
function Size(t: Option<S_Node>): nat
{
  match t
    case None => 0
    case Some(n) => 1 + Size(n.f_left) + Size(n.f_right)
}

function Sum(t: Option<S_Node>): int
{
  match t
    case None => 0
    case Some(n) => n.f_value as int + Sum(n.f_left) + Sum(n.f_right)
}

predicate Within(t: Option<S_Node>, bound: int)
{
  match t
    case None => true
    case Some(n) => -bound <= n.f_value as int <= bound && Within(n.f_left, bound) && Within(n.f_right, bound)
}

// The sum of a tree is at most the bound times the size in magnitude, when each value is inside the bound.
lemma SumBound(t: Option<S_Node>)
  requires Within(t, 1000000)
  ensures -1000000 * Size(t) <= Sum(t) <= 1000000 * Size(t)
{
  match t
    case None =>
    case Some(n) =>
      SumBound(n.f_left);
      SumBound(n.f_right);
}
