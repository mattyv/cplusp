#include <cstdint>
#include <memory>
#include <carrier.h>
#include <sys/uio.h>

void through_method(const std::unique_ptr<Carrier>& p) {
  *p->get() = 1;
  p->ref() = 1;
  p->view()[0] = 1;
}

void through_copy(const std::unique_ptr<iovec>& p) {
  iovec v = *p;
  *static_cast<int32_t*>(v.iov_base) = 1;
}

void through_const_ref(const std::unique_ptr<Carrier>& p) {
  const Carrier& c = *p;
  *c.raw = 1;
}

//@ requires p != nullptr
//@ ensures result == (p->sp.size() == 0 ? 0 : 1)
int32_t reads(const std::unique_ptr<Carrier>& p) {
  return p->sp.size() == 0 ? 0 : 1;
}
