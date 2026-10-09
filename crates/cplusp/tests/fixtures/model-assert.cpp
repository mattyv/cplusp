#include <cstddef>
#include <cstdint>
#include <span>

// Assert and apply lines give the prover the steps it cannot find alone, decision 0099.
//@ ensures result == Sum(bytes) % 256
uint8_t checksum(std::span<const uint8_t> bytes) {
  uint32_t acc = 0;
  //@ invariant 0 <= i <= bytes.size()
  //@ invariant acc == Sum(bytes[..i]) % 256
  for (size_t i = 0; i < bytes.size(); ++i) {
    //@ assert bytes[..i + 1][..i] == bytes[..i]
    acc = (acc + bytes[i]) % 256;
  }
  //@ assert bytes[..bytes.size()] == bytes
  return static_cast<uint8_t>(acc);
}

//@ ensures result == Sum(bytes) % 256
uint8_t checksum_by_lemma(std::span<const uint8_t> bytes) {
  uint32_t acc = 0;
  //@ invariant 0 <= i <= bytes.size()
  //@ invariant acc == Sum(bytes[..i]) % 256
  for (size_t i = 0; i < bytes.size(); ++i) {
    //@ apply SumStep(bytes, i)
    acc = (acc + bytes[i]) % 256;
  }
  //@ apply SumAll(bytes)
  return static_cast<uint8_t>(acc);
}

// A loop contract in a member function that writes its object reads the object as the body has it.
struct Counter {
  int32_t n_;

  //@ requires n_ == 0
  //@ ensures n_ == 10
  void fill() {
    int32_t i = 0;
    //@ invariant 0 <= i <= 10 && n_ == i
    //@ decreases 10 - i
    while (i < 10) {
      n_ += 1;
      i += 1;
    }
  }
};
