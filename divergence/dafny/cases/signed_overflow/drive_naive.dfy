// The naive driver: the naive model takes unbounded ints, and the harness gives it the whole int32 range.
method Main() {
  for i := 0 to |arg0| {
    var r := add(arg0[i], arg1[i]);
    print r, "\n";
  }
}
