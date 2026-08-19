#pragma once

#include "mcmini/model/transition.hpp"

namespace model {
namespace transitions {

struct process_abort : public model::transition {
 public:
  process_abort(state::runner_id_t executor) : transition(executor) {}
  ~process_abort() = default;

  status modify(model::mutable_state& s) const override {
    // We ensure that aborting is never enabled. This ensures that it will never
    // be explored by any model checking algorithm
    return status::exists;
  }

  bool aborts_program_execution() const override { return true; }

  std::string to_string() const override { return "abort(2) (syscall)"; }

  // MARK: Model checking functions
  //
  // `modify` above writes no state and is never disabled, so this transition
  // commutes with every other one and can always be enabled alongside one.
  bool depends(const model::transition* t) const { return false; }
  bool coenabled_with(const model::transition* t) const { return true; }
};

}  // namespace transitions
}  // namespace model
