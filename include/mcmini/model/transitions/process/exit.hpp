#pragma once

#include "mcmini/model/transition.hpp"

namespace model {
namespace transitions {

struct process_exit : public model::transition {
 public:
  int exit_code = -1;
  process_exit(state::runner_id_t executor) : process_exit(executor, -1) {}
  process_exit(state::runner_id_t executor, int exit_code)
      : transition(executor), exit_code(exit_code) {}
  ~process_exit() = default;

  status modify(model::mutable_state& s) const override {
    // We ensure that exiting is never enabled. This ensures that it will never
    // be explored by any model checking algorithm
    return status::exists;
  }

  int program_exit_code() const override { return exit_code; }

  std::string to_string() const override { return "exit(2) (syscall)"; }

  // MARK: Model checking functions
  //
  // `modify` above writes no state and is never disabled, so this transition
  // commutes with every other one and can always be enabled alongside one.
  bool depends(const model::transition* t) const { return false; }
  bool coenabled_with(const model::transition* t) const { return true; }
};

}  // namespace transitions
}  // namespace model
