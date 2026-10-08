// The specification functions of model-spec.cpp, decision 0079.
function Max(a: int, b: int): int {
  if a < b then b else a
}

predicate Leaf(n: S_Node) {
  |n.f_children| == 0
}

// No child has an empty prefix. A ghost predicate, decision 0080.
ghost predicate Wellformed(n: S_Node) {
  forall i :: 0 <= i < |n.f_children| ==> |n.f_children[i].f_prefix| > 0
}

// A quantifier over all integers, which only a ghost predicate may hold, decision 0080.
ghost predicate Above(a: int) {
  exists b: int :: b < a
}
