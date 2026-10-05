// The differential driver, shared by both models: true or false per input, over the whole range of both arguments.
method Main() {
  for i := 0 to |arg0| {
    var r := below(arg0[i] as int32, arg1[i] as uint64);
    print r, "\n";
  }
}
