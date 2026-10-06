#include <cstdint>
#include <coroutine>

//@ requires count >= 0
int32_t sum_all(int32_t count, ...);

int32_t three() {
  return sum_all(2, 1, 2);  // BANNED
}

struct Task {
  struct promise_type {
    Task get_return_object() { return {}; }
    std::suspend_never initial_suspend() noexcept { return {}; }
    std::suspend_never final_suspend() noexcept { return {}; }
    void return_void() {}
    void unhandled_exception() {}
  };
};

// The compiler adds an await for the start and one for the end of every coroutine.
// The gate reports those on the line of the function name. So that line is banned too.
Task waits() {  // BANNED
  co_await std::suspend_never{};  // BANNED
}

Task returns() {  // BANNED
  co_return;  // BANNED
}

struct Counter {
  struct promise_type {
    int32_t last = 0;
    Counter get_return_object() { return {}; }
    std::suspend_always initial_suspend() noexcept { return {}; }
    std::suspend_always final_suspend() noexcept { return {}; }
    std::suspend_always yield_value(int32_t v) {
      last = v;
      return {};
    }
    void return_void() {}
    void unhandled_exception() {}
  };
};

Counter counts() {  // BANNED
  co_yield 1;  // BANNED
}
