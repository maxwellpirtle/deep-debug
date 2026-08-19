#pragma once

#include "mcmini/model/objects/semaphore.hpp"
#include "mcmini/model/transitions/semaphore/semaphore_transition.hpp"

namespace model {
namespace transitions {

struct sem_destroy : public semaphore_transition {
 public:
  sem_destroy(runner_id_t executor, state::objid_t sem_id)
      : semaphore_transition(executor, sem_id) {}
  ~sem_destroy() = default;
  status modify(model::mutable_state& s) const override {
    using namespace model::objects;
    // Destroy is always enabled, so this returns `status::exists`
    // unconditionally -- the same shape as `mutex_init::modify`. Destroying a
    // semaphore that still has blocked waiters is undefined under POSIX and is
    // deliberately not detected: the model has no waiter queue, since
    // `sem_wait` disables rather than decrementing past zero.
    //
    // `semaphore(semaphore::destroyed)` resolves to
    // `explicit semaphore(state s) : semaphore(s, 0) {}` and so also zeroes the
    // count. That is intended: nothing reads a destroyed semaphore's count.
    s.add_state_for_obj(sem_id, new semaphore(semaphore::destroyed));
    return status::exists;
  }
  std::string to_string() const override {
    return "sem_destroy(semaphore:" + std::to_string(sem_id) + ")";
  }
};
}  // namespace transitions
}  // namespace model
