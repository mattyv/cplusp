// Model B: the same file as model A. No rule changes it.
// The tree is one recursive datatype, and the height bound is the rule of the case stack_depth.
// A std::vector<uint8_t> is a seq<uint8>, a std::span of it is a seq too, a std::optional is an Option, decision 0029, and a
// std::vector<Node> is a seq<Node>. The tree is one recursive datatype. Height, Wellformed and Stored are the specification functions
// the contract names.
newtype uint8 = x: int | 0 <= x < 0x100
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Option<T> = None | Some(value: T)
datatype Node = Node(prefix: seq<uint8>, value: Option<int32>, children: seq<Node>)

// The number of nodes on the longest path down from n, n included.
function Height(n: Node): nat
  decreases n, 1
{
  1 + MaxHeight(n, 0)
}

function MaxHeight(n: Node, i: nat): nat
  requires i <= |n.children|
  decreases n, 0, |n.children| - i
{
  if i == |n.children| then 0
  else
    var h := Height(n.children[i]);
    var rest := MaxHeight(n, i + 1);
    if h > rest then h else rest
}

lemma ChildIsLower(n: Node, i: nat, k: nat)
  requires k <= i < |n.children|
  ensures Height(n.children[i]) <= MaxHeight(n, k)
  decreases i - k
{
  if k < i {
    ChildIsLower(n, i, k + 1);
  }
}

// No child has an empty prefix, and no two children of a node start with the same byte.
predicate Wellformed(n: Node)
  decreases n
{
  (forall i :: 0 <= i < |n.children| ==> |n.children[i].prefix| > 0)
  && (forall i, j :: 0 <= i < j < |n.children| ==> n.children[i].prefix[0] != n.children[j].prefix[0])
  && (forall i :: 0 <= i < |n.children| ==> Wellformed(n.children[i]))
}

// The tree maps the key to v. The key starts below the node's own prefix.
predicate Stored(n: Node, key: seq<uint8>, v: int32)
  decreases n
{
  if |key| == 0 then n.value == Some(v)
  else exists i :: 0 <= i < |n.children| && Through(n.children[i], key) && Stored(n.children[i], key[|n.children[i].prefix|..], v)
}

// The child's prefix starts the key.
predicate Through(c: Node, key: seq<uint8>)
{
  |c.prefix| <= |key| && key[..|c.prefix|] == c.prefix
}

method find(n: Node, key: seq<uint8>) returns (result: Option<int32>)
  requires Wellformed(n)
  requires Height(n) <= 1000
  decreases Height(n)
  ensures forall v :: result == Some(v) <==> Stored(n, key, v)
{
  if |key| == 0 {
    return n.value;
  }
  for i := 0 to |n.children|
    invariant forall k :: 0 <= k < i ==> n.children[k].prefix[0] != key[0]
  {
    if n.children[i].prefix[0] == key[0] {
      var c := n.children[i];
      // Only this child can lead to the key, because no other child starts with key[0].
      assert forall k :: 0 <= k < |n.children| && Through(n.children[k], key) ==> k == i by {
        forall k | 0 <= k < |n.children| && Through(n.children[k], key)
          ensures k == i
        {
          assert n.children[k].prefix[0] == key[0];
        }
      }
      if |c.prefix| > |key| {
        return None;
      }
      for j := 0 to |c.prefix|
        invariant key[..j] == c.prefix[..j]
      {
        if c.prefix[j] != key[j] {
          return None;
        }
      }
      assert Through(c, key);
      ChildIsLower(n, i, 0);
      result := find(c, key[|c.prefix|..]);
      return;
    }
  }
  return None;
}
