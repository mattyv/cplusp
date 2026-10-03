int& first() {
  int local = 1;
  return local;  // BANNED
}

int* address() {
  int local = 1;
  return &local;  // BANNED
}
