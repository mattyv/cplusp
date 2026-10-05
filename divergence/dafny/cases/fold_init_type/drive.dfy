// The differential driver, shared by both models: the sum of each generated sequence. The mitigated run keeps every element
// in the int32 range, as the contract requires. The naive run gets the whole int64 range, where the C++ fold in int is wrong.
method Main() {
  for i := 0 to |arg0| {
    var v: seq<int64> := seq(|arg0[i]|, j requires 0 <= j < |arg0[i]| => arg0[i][j] as int64);
    var r := total(v);
    print r, "\n";
  }
}
