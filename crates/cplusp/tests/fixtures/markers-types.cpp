#include <cstdint>
#include "../../../../include/cplusp.h"

// A plain type is out of view: its fields, its static members and its member functions, decision 0051.
struct CPLUSP_PLAIN("an old record") Record {
  int count = 0;
  int extra = 0;
  static int made;
  int twice() const {
    return count * 2;
  }
  CPLUSP_TRUSTED("reads the count of the old record")
  //@ ensures result >= 0
  int32_t size() const;
};

int Record::made = 0;

// Plain code may use a plain type.
CPLUSP_PLAIN("old code")
int use_record() {
  Record r;
  r.count = 3;
  return r.twice();
}

// Verified code makes no object of a plain type, and reads no field of one.
int32_t make_one() {
  Record r;
  return 0;
}

int32_t read_field(const Record& r) {
  return r.count;
}

// A plain member is plain code, decision 0047.
int32_t call_member(const Record& r) {
  return r.twice();
}

// Verified code may hold a reference to a plain type, and call a trusted member.
int32_t sized(const Record& r) {
  return r.size();
}
