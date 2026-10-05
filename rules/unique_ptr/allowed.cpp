#include <cstddef>
#include <cstdint>
#include <memory>
#include <vector>

struct Command {
  virtual ~Command() = default;
  virtual void run() = 0;
  virtual int32_t peek() const = 0;
};

// A non-const container, so the owned commands may change.
//@ requires cmds.size() <= 1000
//@ requires forall i :: 0 <= i < cmds.size() ==> cmds[i] != nullptr
void run_all(std::vector<std::unique_ptr<Command>>& cmds) {
  for (size_t i = 0; i < cmds.size(); ++i) {
    cmds[i]->run();
  }
}

// A const container gives const access, and a const call is fine.
//@ requires cmds.size() > 0 && cmds[0] != nullptr
//@ ensures result == cmds[0]->peek()
int32_t peek_first(const std::vector<std::unique_ptr<Command>>& cmds) {
  return cmds[0]->peek();
}

//@ requires p != nullptr
//@ ensures result == p->peek()
int32_t peek_one(const std::unique_ptr<Command>& p) {
  return p->peek();
}
