struct S { int a; };
int f() {
  S s; int y;
  y = 1; s.a = y;
  return s.a + y;
}
