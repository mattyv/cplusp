int read_twice(const int* reg) {
  return *reg + *reg;
}

int local() {
  int v = 1;
  return v;
}
