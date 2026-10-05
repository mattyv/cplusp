// The differential driver, shared by both models. The shift count stays below 32 for the mitigated run, as the contract
// requires. The naive run gets the whole range, where the C++ is undefined and the model says 0.
method Main() {
  for i := 0 to |arg0| {
    var r := shl(arg0[i] as bv32, arg1[i] as bv32);
    print r as int, "\n";
  }
}
