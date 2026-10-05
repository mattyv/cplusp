// The differential driver, shared by the naive and the mitigated model, which have one signature. A divisor of zero and the
// one overflowing pair are outside both contracts, so the driver skips them in the same way drive.cpp does.
method Main() {
  for i := 0 to |arg0| {
    var a := arg0[i] as int32;
    var b := arg1[i] as int32;
    if b == 0 || (a == -0x8000_0000 && b == -1) {
      print "skip\n";
    } else {
      var q := quot(a, b);
      var r := rem(a, b);
      print q, " ", r, "\n";
    }
  }
}
