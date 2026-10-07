// The differential driver: a fixed tree, and the find of each generated key. The tree holds the keys 010, 01001, 011, 1 and 22, with
// the values 1 to 5. Its shape is the one that FlashRadixTree builds for them: 01 is a node with no value, because two keys pass it.
// The run takes keys of the bytes 0, 1 and 2, so most of them meet the tree.
method Main() {
  var tree := Node([], None, [
    Node([0, 1], None, [
      Node([0], Some(1), [Node([0, 1], Some(2), [])]),
      Node([1], Some(3), [])
    ]),
    Node([1], Some(4), []),
    Node([2, 2], Some(5), [])
  ]);
  for i := 0 to |arg0| {
    var key: seq<uint8> := seq(|arg0[i]|, j requires 0 <= j < |arg0[i]| => arg0[i][j] as uint8);
    var r := find(tree, key);
    match r
      case None => print "none\n";
      case Some(v) => print v, "\n";
  }
}
