// An enum class is a datatype of its enumerators. Index is the static_cast to size_t, and it gives the declared value of each
// enumerator. A std::array<int32_t, 3> is a seq of length 3. The bound in the contract holds in the model for every Level, because a
// datatype has only the enumerators, so the prover finds it at once. The cast from an integer is a match, and its precondition is that
// the integer is an enumerator, as in the case enum_cast.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint8 = x: int | 0 <= x < 0x100
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

datatype Level = Low | Medium | High

type Table = s: seq<int32> | |s| == 3 witness [0, 0, 0]

function Index(level: Level): uint64 {
  match level
    case Low => 0
    case Medium => 1
    case High => 2
}

method lookup(table: Table, level: Level) returns (result: int32)
  requires Index(level) < 3
  ensures result == table[Index(level)]
{
  result := table[Index(level)];
}

method default_table() returns (result: Table)
  ensures result[0] == 10 && result[1] == 20 && result[2] == 30
{
  result := [10, 20, 30];
}

method high_weight() returns (result: int32)
  ensures result == 30
{
  var t := default_table();
  result := lookup(t, High);
}

method lookup_code(table: Table, code: uint8) returns (result: int32)
  requires code < 3
  ensures result == table[code]
{
  var level: Level;
  match code {
    case 0 => level := Low;
    case 1 => level := Medium;
    case 2 => level := High;
  }
  result := lookup(table, level);
}
