// The specification functions of radix_find, decision 0079. No child has an empty prefix, and no two children of a node start
// with the same byte.
predicate Wellformed(n: S_Node)
  decreases n
{
  (forall i :: 0 <= i < |n.f_children| ==> |n.f_children[i].f_prefix| > 0)
  && (forall i, j :: 0 <= i < j < |n.f_children| ==> n.f_children[i].f_prefix[0] != n.f_children[j].f_prefix[0])
  && (forall i :: 0 <= i < |n.f_children| ==> Wellformed(n.f_children[i]))
}

// The child's prefix starts the key.
predicate Through(c: S_Node, key: seq<uint8>)
{
  |c.f_prefix| <= |key| && key[..|c.f_prefix|] == c.f_prefix
}

// The tree maps the key to v. The key starts below the node's own prefix.
predicate Stored(n: S_Node, key: seq<uint8>, v: int)
  decreases n
{
  if |key| == 0 then n.f_value.Some? && n.f_value.value as int == v
  else exists i :: 0 <= i < |n.f_children| && Through(n.f_children[i], key) && Stored(n.f_children[i], key[|n.f_children[i].f_prefix|..], v)
}

// The number of nodes on the longest path down from n, n included. Each child is lower than its node, and Dafny checks that
// against the body.
function Height(n: S_Node): nat
  ensures forall i :: 0 <= i < |n.f_children| ==> Height(n.f_children[i]) < Height(n)
  decreases n, 1
{
  1 + MaxHeight(n, 0)
}

// The greatest height among the children of n from the i-th on.
function MaxHeight(n: S_Node, i: nat): nat
  requires i <= |n.f_children|
  ensures forall k :: i <= k < |n.f_children| ==> Height(n.f_children[k]) <= MaxHeight(n, i)
  decreases n, 0, |n.f_children| - i
{
  if i == |n.f_children| then 0
  else
    var h := Height(n.f_children[i]);
    var rest := MaxHeight(n, i + 1);
    if h > rest then h else rest
}
