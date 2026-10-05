#include <cstdint>
#include <memory>

// The pointer to implementation. The class declares its members and holds one, a unique_ptr to an Impl that the header does not
// define. The Impl and the bodies come after, in the same file here. The destructor and the moves are defined out of line, after
// Impl is complete, because the unique_ptr needs the full type to delete it. The invariant is valid(), decision 0028, and it looks
// through the pointer.
// The classic pimpl class also has a move assignment, declared in the class and defined `= default` out of line:
// `Account& operator=(Account&&) noexcept;`. The gate refuses the declaration at its line: "Operator overloading: outside its
// limit. Limit: A const member, or a free function with const or by-value parameters. No assignment, compound assignment,
// increment or decrement operator unless it is `= default` or `= delete`. Use a const operator with no side effects, or a named
// function." The definition is `= default`, but the declaration is not. An in-class `= default` cannot do, because the unique_ptr
// needs the complete Impl at that point. So the move assignment is deleted here, and an account changes owner by the move constructor.
class Account {
 public:
  //@ requires 0 <= opening <= 1000000
  //@ ensures valid() && balance() == opening
  explicit Account(int32_t opening);

  Account(const Account&) = delete;
  Account& operator=(const Account&) = delete;

  //@ requires other.valid()
  //@ ensures valid() && balance() == old(other.balance()) && !other.valid()
  Account(Account&& other) noexcept;
  Account& operator=(Account&&) = delete;

  ~Account();

  //@ ensures result == (impl_ != nullptr && 0 <= impl_->balance && impl_->balance <= 1000000)
  bool valid() const;

  //@ requires valid()
  //@ ensures result == impl_->balance
  int32_t balance() const;

  //@ requires valid() && 0 <= amount <= 1000000 && balance() <= 1000000 - amount
  //@ ensures valid() && balance() == old(balance()) + amount
  void deposit(int32_t amount);

 private:
  struct Impl;
  std::unique_ptr<Impl> impl_;
};

struct Account::Impl {
  int32_t balance;

  explicit Impl(int32_t b) : balance(b) {}
};

Account::Account(int32_t opening) : impl_(std::make_unique<Impl>(opening)) {}

Account::Account(Account&& other) noexcept = default;

Account::~Account() = default;

bool Account::valid() const {
  return impl_ != nullptr && 0 <= impl_->balance && impl_->balance <= 1000000;
}

int32_t Account::balance() const {
  return impl_->balance;
}

void Account::deposit(int32_t amount) {
  impl_->balance += amount;
}

//@ requires 0 <= opening <= 500000 && 0 <= amount <= 500000
//@ ensures result == opening + amount
int32_t open_and_deposit(int32_t opening, int32_t amount) {
  Account account(opening);
  account.deposit(amount);
  return account.balance();
}
