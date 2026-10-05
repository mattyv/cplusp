#include <cstdint>
#include <utility>

// RAII, move-only. A handle acquires in its constructor and releases in its destructor. The number of open handles is a global
// the contracts list, so the release is something a caller can see. The valid() predicate of decision 0028 says the handle is
// open: it holds from the constructor until the handle is moved from or destroyed. Copying is deleted. A move hands the open
// handle to the new object and leaves the old one closed, so the destructor of the old one releases nothing.
// The classic move-only class also has a move assignment, `Handle& operator=(Handle&& other) noexcept`. The gate refuses it
// at that line: "Operator overloading: outside its limit. Limit: A const member, or a free function with const or by-value
// parameters. No assignment, compound assignment, increment or decrement operator unless it is `= default` or `= delete`.
// Use a const operator with no side effects, or a named function." So the move assignment is deleted here. A handle changes
// owner by the move constructor, and an existing handle is never overwritten.
int32_t open_count = 0;

class Handle {
 public:
  //@ requires 0 <= open_count < 1000
  //@ modifies open_count
  //@ ensures valid() && open_count == old(open_count) + 1
  Handle() : open_(true) { open_count += 1; }

  Handle(const Handle&) = delete;
  Handle& operator=(const Handle&) = delete;
  Handle& operator=(Handle&&) = delete;

  //@ requires other.valid()
  //@ ensures valid() && !other.valid()
  Handle(Handle&& other) noexcept : open_(other.open_) { other.open_ = false; }

  //@ requires 0 <= open_count <= 1000
  //@ modifies open_count
  //@ ensures open_count == old(open_count) - (old(valid()) ? 1 : 0)
  ~Handle() {
    if (open_) {
      open_count -= 1;
    }
  }

  //@ ensures result == open_
  bool valid() const { return open_; }

 private:
  bool open_;
};

// The handle lives for the block and no longer. Inside the block the count is one higher. After it the count is back.
//@ requires 0 <= open_count < 1000
//@ modifies open_count
//@ ensures open_count == old(open_count) && result == old(open_count) + 1
int32_t count_inside_block() {
  int32_t inside = 0;
  {
    Handle h;
    inside = open_count;
  }
  return inside;
}

// A function that takes the handle by rvalue reference owns it. The handle it moves into a local dies at the end of the function.
// The caller's handle is closed after the call, and its destructor releases nothing.
//@ requires h.valid() && 0 < open_count <= 1000
//@ modifies open_count
//@ ensures open_count == old(open_count) - 1 && !h.valid()
void consume(Handle&& h) {
  Handle owned = std::move(h);
}

//@ requires 0 <= open_count < 1000
//@ modifies open_count
//@ ensures open_count == old(open_count)
void hand_over() {
  Handle h;
  consume(std::move(h));
}
