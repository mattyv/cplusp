// The differential driver: true or false, spelled as Dafny prints a bool.
#include <cstddef>
#include <cstdint>
#include <cstdio>

#include "inputs.h"

bool below(int32_t i, std::size_t n);

int main() {
  for (std::size_t i = 0; i < runs; ++i) {
    std::printf("%s\n", below(arg0[i], arg1[i]) ? "true" : "false");
  }
  return 0;
}
