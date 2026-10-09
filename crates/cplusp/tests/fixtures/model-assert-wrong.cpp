#include <cstdint>
// An assert line that may not hold, and a lemma whose requires line may not hold, are named at their lines, decision 0099.
int32_t same(int32_t x) {
  //@ assert x >= 0
  return x;
}

int32_t step(int32_t x) {
  //@ apply Positive(x)
  return x;
}
