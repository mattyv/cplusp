int read_twice(volatile int* reg) {  // BANNED
  return *reg + *reg;
}

int read_ref(volatile int& reg) {  // BANNED
  return reg;
}

int local() {
  volatile int v = 1;  // BANNED
  return v;
}

struct Device {
  volatile int status = 0;  // BANNED
};
