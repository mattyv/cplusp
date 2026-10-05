#include <cstdint>

// A function that calls a function it is given. The first choice is std::function, and the gate refuses it at that line: "Function
// pointers, `std::function`: allowed only in trusted code. Indirect calls need contracts on the target. Use direct calls or a template
// parameter, or mark the function trusted with a reason." The second choice is a lambda passed to the function, and the gate refuses it
// too: "Lambdas: outside its limit. Limit: Passed directly to a std:: call, capturing by value only. No capture by reference, no capture
// of this, and not mutable. Use a lambda passed straight to the algorithm, capturing by value." What passes is a functor type as a
// template parameter, a struct with an operator() that is const and has its own contract. A call is then a direct call. The template
// has no model, and each functor type it is used at gets its own, as in the folder templates. Both functors here are total, with no
// precondition, because a contract on the template cannot yet name the precondition of the functor it is given.
// ponytail: total functors only. The upgrade is a contract form that names the precondition of the functor.
struct Halve {
  //@ ensures result == x / 2
  int32_t operator()(int32_t x) const { return x / 2; }
};

struct CapAt {
  int32_t limit;

  //@ ensures result == (x < limit ? x : limit)
  int32_t operator()(int32_t x) const { return x < limit ? x : limit; }
};

//@ ensures result == f(f(x))
template <typename F>
int32_t apply_twice(const F& f, int32_t x) {
  return f(f(x));
}

// Two callers, one for each functor type. The prover proves each result from the contract of the functor alone.
//@ ensures result == x / 4
int32_t quarter(int32_t x) {
  return apply_twice(Halve{}, x);
}

//@ ensures result == (x < limit ? x : limit)
int32_t cap_twice(int32_t x, int32_t limit) {
  return apply_twice(CapAt{limit}, x);
}
