// The pointer to implementation is a datatype that holds an Option of the Impl datatype, as a unique_ptr member is, decision 0029.
// The invariant is a predicate that looks through the Option. Where the Impl is defined, and in which file, is a matter of
// compilation and has no part in the model. A move is a copy, and the source holds nothing afterwards. The model has no destructor
// call to show, since the destructor of the member releases nothing the model can see.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Option<T> = None | Some(value: T)

datatype Impl = Impl(balance: int32)

datatype Account = Account(impl_: Option<Impl>)

predicate ValidAccount(a: Account) { a.impl_.Some? && 0 <= a.impl_.value.balance <= 1_000_000 }

function balance(a: Account): int32
  requires ValidAccount(a)
{
  a.impl_.value.balance
}

method MakeAccount(opening: int32) returns (a: Account)
  requires 0 <= opening <= 1_000_000
  ensures ValidAccount(a) && balance(a) == opening
{
  a := Account(Some(Impl(opening)));
}

method MoveAccount(other: Account) returns (other': Account, a: Account)
  requires ValidAccount(other)
  ensures ValidAccount(a) && balance(a) == balance(other) && !ValidAccount(other')
{
  a := other;
  other' := Account(None);
}

method deposit(a: Account, amount: int32) returns (a': Account)
  requires ValidAccount(a) && 0 <= amount <= 1_000_000 && balance(a) as int <= 1_000_000 - amount as int
  ensures ValidAccount(a') && balance(a') as int == balance(a) as int + amount as int
{
  a' := Account(Some(Impl(a.impl_.value.balance + amount)));
}

method open_and_deposit(opening: int32, amount: int32) returns (result: int32)
  requires 0 <= opening <= 500_000 && 0 <= amount <= 500_000
  ensures result as int == opening as int + amount as int
{
  var account := MakeAccount(opening);
  account := deposit(account, amount);
  result := balance(account);
}
