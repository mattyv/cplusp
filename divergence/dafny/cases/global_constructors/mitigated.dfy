// Model B: no global has a dynamic initializer. `derived_value` computes the value from `base_value` when it is called.
// The order in which the files initialize does not enter the model, because fixed.cpp does not depend on it.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

const base_value: int32 := 5

function derived_value(): int32 { base_value + 1 }

method read_derived() returns (result: int32)
  ensures result == base_value + 1
{
  result := derived_value();
}
