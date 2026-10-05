// The differential driver, shared by both models: the product as an int64, over the whole int32 range of both factors.
method Main() {
  for i := 0 to |arg0| {
    var r := product(arg0[i] as int32, arg1[i] as int32);
    print r, "\n";
  }
}
