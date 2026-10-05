// The differential driver: the mitigated model on the generated inputs, one line per input. The harness compares the lines
// with what drive.cpp prints. The inputs stay in half the int32 range, so the sum fits, as the model's contract requires.
method Main() {
  for i := 0 to |arg0| {
    var r := add(arg0[i] as int32, arg1[i] as int32);
    print r, "\n";
  }
}
