struct S { bool a; };
bool f() {
  S s; bool y;
  y = true; s.a = y;
  return s.a && y;
}
