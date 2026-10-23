#include <cstddef>
#include <cstdint>
#include "../../include/cplusp.h"

// A bump arena. acquire(size) hands out the next size bytes of a pool and returns the index of the first one. release() gives all of it
// back at once, and the next acquire starts at index 0 again. The pool is one block of 4096 bytes made with new, so the allocation is
// trusted code, and a verified caller sees only the contracts. The one number the contracts need is how much of the pool is in use, and it
// is a static data member, `Arena::used_`, listed in `modifies` as in the folder global_state. The usual place for it is a
// static local in a function, such as `static size_t used = 0;` inside acquire, and the gate refuses that at that line: "A function-local
// static variable: not allowed in verified code. Its state has no name a caller's contract can list, so no caller can prove anything
// about a call that changes it. Use a static data member or a global, listed in reads or modifies." The body of acquire is not in this
// folder. It makes the pool with `new uint8_t[4096]`, and the gate refuses that line under the row raw_allocation: "`new` / `delete`,
// `malloc` / `free`: allowed only in trusted code. Allocation is trusted. Ownership goes through RAII types. Use std::unique_ptr or a
// container, or mark the function trusted with a reason." The body is in trusted.cpp, which the gate refuses, and this file keeps
// the declarations and the callers. The refusal is quoted here.
class Arena {
 public:
  Arena() = delete;

  //@ reads Arena::used_
  //@ ensures result == (Arena::used_ <= 4096)
  static bool valid() { return used_ <= 4096; }

  //@ requires valid()
  //@ reads Arena::used_
  //@ ensures result == Arena::used_
  static size_t used() { return used_; }

  CPLUSP_TRUSTED("the pool is one block made with new, and an index handed out stays inside it")
  //@ requires valid() && 0 < size && size <= 4096 - used()
  //@ modifies Arena::used_
  //@ ensures valid() && result == old(used()) && used() == old(used()) + size
  static size_t acquire(size_t size);

  CPLUSP_TRUSTED("release only moves the start of the free part back to the front of the pool")
  //@ modifies Arena::used_
  //@ ensures valid() && used() == 0
  static void release();

 private:
  static size_t used_;
};

size_t Arena::used_ = 0;

// A verified caller. Two blocks, one after the other. The second starts where the first ends.
//@ requires Arena::valid() && 0 < n && 0 < m && n + m <= 4096 - Arena::used()
//@ modifies Arena::used_
//@ ensures Arena::valid() && result == old(Arena::used()) + n && Arena::used() == old(Arena::used()) + n + m
size_t second_block(size_t n, size_t m) {
  Arena::acquire(n);
  return Arena::acquire(m);
}

// A new frame: release everything, and the first block starts at the front.
//@ requires 0 < size && size <= 4096
//@ modifies Arena::used_
//@ ensures Arena::valid() && result == 0 && Arena::used() == size
size_t first_block_of_new_frame(size_t size) {
  Arena::release();
  return Arena::acquire(size);
}
