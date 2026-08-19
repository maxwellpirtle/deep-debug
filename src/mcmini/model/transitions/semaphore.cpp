#include "mcmini/mem.h"
#include "mcmini/model/exception.hpp"
#include "mcmini/model/transitions/semaphore/callbacks.hpp"
#include "mcmini/model/transitions/semaphore/sem_destroy.hpp"
#include "mcmini/model/transitions/semaphore/sem_init.hpp"
#include "mcmini/model/transitions/semaphore/sem_post.hpp"
#include "mcmini/model/transitions/semaphore/sem_wait.hpp"

using namespace model;
using namespace objects;

model::transition* sem_init_callback(runner_id_t p,
                                     const volatile runner_mailbox& rmb,
                                     model_to_system_map& m) {
  // Fetch the remote object
  int count;
  sem_t* remote_sem;
  memcpy_v(&remote_sem, (volatile void*)rmb.cnts, sizeof(sem_t*));
  memcpy_v(&count, (volatile void*)(rmb.cnts + sizeof(sem_t*)), sizeof(int));

  // Locate the corresponding model of this object
  if (!m.contains(remote_sem)) m.observe_object(remote_sem, new semaphore());

  const state::objid_t model_sem = m.get_model_of_object(remote_sem);
  return new transitions::sem_init(p, model_sem, count);
}

model::transition* sem_post_callback(runner_id_t p,
                                     const volatile runner_mailbox& rmb,
                                     model_to_system_map& m) {
  sem_t* remote_sem;
  memcpy_v(&remote_sem, (volatile void*)rmb.cnts, sizeof(sem_t*));

  // TODO: Add code from Gene's PR here to check for initialized semaphores
  // NOTE: this guard must precede any query of model state below. An address
  // the model has never seen resolves to `model::invalid_objid`, and indexing
  // the model with that is an out-of-range lookup no `verify_using` catch
  // clause handles.
  if (!m.contains(remote_sem))
    throw undefined_behavior_exception(
        "Attempting to post to an uninitialized semaphore");

  const state::objid_t model_sem = m.get_model_of_object(remote_sem);
  if (m.get_current_model_state()
          .get_state_of_object<semaphore>(model_sem)
          ->is_destroyed())
    throw undefined_behavior_exception(
        "Attempting to post to a semaphore that has been destroyed");

  return new transitions::sem_post(p, model_sem);
}

model::transition* sem_wait_callback(runner_id_t p,
                                     const volatile runner_mailbox& rmb,
                                     model_to_system_map& m) {
  sem_t* remote_sem;
  memcpy_v(&remote_sem, (volatile void*)rmb.cnts, sizeof(sem_t*));

  // TODO: Add code from Gene's PR here to check for initialized semaphores
  if (!m.contains(remote_sem))
    throw undefined_behavior_exception(
        "Attempting to wait on an uninitialized semaphore");

  const state::objid_t model_sem = m.get_model_of_object(remote_sem);
  // Use-after-destroy is detected here, where the next operation of the thread
  // is determined, and NOT by returning `status::undefined` from
  // `sem_wait::modify`. That route reaches `program::model_execution_of`, which
  // throws a plain `std::runtime_error` no catch clause in `verify_using`
  // handles; worse, `apply_to` collapses `undefined` into `disabled`, dropping
  // the runner out of `get_enabled_runners()` so the program is reported as a
  // deadlock -- a semantically wrong violation kind that reads as a right one.
  if (m.get_current_model_state()
          .get_state_of_object<semaphore>(model_sem)
          ->is_destroyed())
    throw undefined_behavior_exception(
        "Attempting to wait on a semaphore that has been destroyed");

  return new transitions::sem_wait(p, model_sem);
}

model::transition* sem_destroy_callback(runner_id_t p,
                                        const volatile runner_mailbox& rmb,
                                        model_to_system_map& m) {
  sem_t* remote_sem;
  memcpy_v(&remote_sem, (volatile void*)rmb.cnts, sizeof(sem_t*));

  if (!m.contains(remote_sem))
    throw undefined_behavior_exception(
        "Attempting to destroy an uninitialized semaphore");

  const state::objid_t model_sem = m.get_model_of_object(remote_sem);
  // Destroying an already-destroyed semaphore is undefined under POSIX for the
  // same reason waiting on one is, and is guarded the same way. Note that
  // `sem_init` on a destroyed semaphore is deliberately NOT guarded:
  // re-initialising a destroyed semaphore is legal.
  if (m.get_current_model_state()
          .get_state_of_object<semaphore>(model_sem)
          ->is_destroyed())
    throw undefined_behavior_exception(
        "Attempting to destroy a semaphore that has already been destroyed");

  return new transitions::sem_destroy(p, model_sem);
}
