#include <cstdint>
#include <memory>
#include <vector>

struct Command {
  virtual ~Command() = default;
  virtual void run() = 0;
};

void run_first(const std::vector<std::unique_ptr<Command>>& cmds) {
  cmds[0]->run();  // BANNED
}

void run_one(const std::unique_ptr<Command>& p) {
  p->run();  // BANNED
}

void run_deref(const std::unique_ptr<Command>& p) {
  (*p).run();  // BANNED
}
