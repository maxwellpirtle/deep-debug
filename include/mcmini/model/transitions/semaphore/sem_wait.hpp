#pragma once

#include "mcmini/model/objects/semaphore.hpp"
#include "mcmini/model/transitions/semaphore/semaphore_transition.hpp"

namespace model {
namespace transitions {

struct sem_wait : public semaphore_transition {
 public:
  sem_wait(runner_id_t executor, state::objid_t sem_id)
      : semaphore_transition(executor, sem_id) {}
  ~sem_wait() = default;
  status modify(model::mutable_state& s) const override {
    using namespace model::objects;
    const semaphore* sem = s.get_state_of_object<semaphore>(sem_id);
    if (sem->will_block()) {
      return status::disabled;
    }
    s.add_state_for_obj(sem_id, new semaphore(sem->count() - 1));
    return status::exists;
  }
  std::string to_string() const override {
    return "sem_wait(semaphore:" + std::to_string(sem_id) + ")";
  }
};
}  // namespace transitions
}  // namespace model
