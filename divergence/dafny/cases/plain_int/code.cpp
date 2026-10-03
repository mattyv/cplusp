//@ requires -1073741824 <= x < 1073741824
//@ ensures result == 2 * x
int twice(int x) {
  return 2 * x;
}
