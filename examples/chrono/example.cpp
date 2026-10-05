#include <chrono>
#include <cstdint>

// A duration in milliseconds, as std::chrono has it. The type is std::chrono::duration<int64_t, std::milli> on this toolchain, a value
// that holds one signed 64-bit count, and the model of it is that count as an int64. The standard asks for 45 bits only, so the width
// is an assumption about the library. The sum of two is the sum of the counts. The standard does not check the overflow, and signed
// overflow is undefined, so the contract carries it as a precondition on the exact integers. The templates row says "Type parameters
// only, no specialisation", and it does not apply here. The standard templates take non-type parameters, such as the ratio 1 to 1000
// in the type of a millisecond. This code only uses them. It declares no template, so the gate has nothing to refuse.
//@ requires -0x8000000000000000 <= a.count() + b.count() <= 0x7FFFFFFFFFFFFFFF
//@ ensures result.count() == a.count() + b.count()
std::chrono::milliseconds add(std::chrono::milliseconds a, std::chrono::milliseconds b) {
  return a + b;
}

// A verified caller: a deadline is a start and a timeout.
//@ requires 0 <= start.count() && start.count() <= 1000000000000 && 0 <= timeout.count() && timeout.count() <= 1000000000000
//@ ensures result.count() == start.count() + timeout.count()
std::chrono::milliseconds deadline(std::chrono::milliseconds start, std::chrono::milliseconds timeout) {
  return add(start, timeout);
}

//@ ensures result.count() == 2500
std::chrono::milliseconds one_and_a_half_seconds_after_one() {
  return deadline(std::chrono::milliseconds{1000}, std::chrono::milliseconds{1500});
}
