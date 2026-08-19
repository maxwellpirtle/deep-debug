#include "../include/mcmini/misc/cond/cond_var_arbitrary_policy.hpp"
#include "mcmini/mem.h"
#include "mcmini/model/exception.hpp"
#include "mcmini/model/objects/mutex.hpp"
#include "mcmini/model/transitions/condition_variables/callbacks.hpp"
#include "mcmini/model/transitions/static_init_registration.hpp"
#include "mcmini/real_world/mailbox/mailbox_payload.h"

using namespace model;
using namespace objects;

model::transition *cond_init_callback(runner_id_t p,
                                      const volatile runner_mailbox &rmb,
                                      model_to_system_map &m) {
  // Fetch the remote object
  pthread_cond_t *remote_cond;
  memcpy_v(&remote_cond, (volatile void *)rmb.cnts, sizeof(pthread_cond_t *));

  // Locate the corresponding model of this object
  if (!m.contains(remote_cond)) {
    // FIXME: Allow dynamic selection of wakeup policies.
    // For now, we hard-code it here. Not great, but at least
    // we can change it relatively easily still
    ConditionVariablePolicy *policy = new ConditionVariableArbitraryPolicy();
    m.observe_object(remote_cond,
                     new condition_variable(
                         condition_variable::state::cv_initialized, policy));
  }

  state::objid_t const cond = m.get_model_of_object(remote_cond);
  return new transitions::condition_variable_init(p, cond);
}

model::transition *cond_waiting_thread_enqueue_callback(
    runner_id_t p, const volatile runner_mailbox &rmb, model_to_system_map &m) {
  pthread_cond_t *remote_cond;
  pthread_mutex_t *remote_mut;
  memcpy_v(&remote_cond, (volatile void *)rmb.cnts, sizeof(pthread_cond_t *));
  memcpy_v(&remote_mut, (volatile void *)(rmb.cnts + sizeof(pthread_cond_t *)),
           sizeof(pthread_mutex_t *));

  // Payload layout [cond*:8][mut*:8][cond_flag:1][mut_flag:1] (D-01): the
  // wrapper classified both primitives in-process for THIS transition and
  // wrote one flag byte per pointer, in pointer order.
  const uint8_t cond_flag = mcmini_payload_read_flag(rmb.cnts, 2, 0);
  const uint8_t mutex_flag = mcmini_payload_read_flag(rmb.cnts, 2, 1);

  transitions::ensure_primitive_initialized(
      m, remote_cond, cond_flag,
      []() {
        return new condition_variable(condition_variable::cv_initialized);
      },
      "Attempting to wait on an uninitialized condition variable");

  // NOTE (D-11 residual gap): the wrapper computes the mutex flag at the
  // enqueue site while the caller still HOLDS the mutex, and a locked static
  // mutex is not byte-equal to its all-zero initializer pattern -- so a held
  // static mutex honestly reads not-static here. Every path reachable from
  // main is safe regardless: the mutex was already observed at its own lock,
  // and the helper's contains() guard short-circuits before the flag is
  // consulted (D-09). The only exposure is a DMTCP-restart path on which this
  // enqueue is the mutex's FIRST observation; that false-UB case is a
  // documented residual gap whose fix needs INIT-F1/INIT-F2 provenance (out
  // of scope this milestone). At the COND_WAIT write sites the wrapper has
  // already unlocked the mutex, so the flag read in cond_wait_callback below
  // is exact.
  transitions::ensure_primitive_initialized(
      m, remote_mut, mutex_flag, []() { return new mutex(mutex::unlocked); },
      "Attempting to wait on a condition "
      "variable with an uninitialized mutex");

  state::objid_t const cond = m.get_model_of_object(remote_cond);
  state::objid_t const mut = m.get_model_of_object(remote_mut);
  return new transitions::condition_variable_enqueue_thread(p, cond, mut);
}

model::transition *cond_wait_callback(runner_id_t p,
                                      const volatile runner_mailbox &rmb,
                                      model_to_system_map &m) {
  pthread_cond_t *remote_cond;
  pthread_mutex_t *remote_mut;
  memcpy_v(&remote_cond, (volatile void *)rmb.cnts, sizeof(pthread_cond_t *));
  memcpy_v(&remote_mut, (volatile void *)(rmb.cnts + sizeof(pthread_cond_t *)),
           sizeof(pthread_mutex_t *));

  // Payload layout [cond*:8][mut*:8][cond_flag:1][mut_flag:1] (D-01).
  const uint8_t cond_flag = mcmini_payload_read_flag(rmb.cnts, 2, 0);
  const uint8_t mutex_flag = mcmini_payload_read_flag(rmb.cnts, 2, 1);

  // Same wording as the enqueue callback above (D-10): enqueue and wait are
  // the two halves of one user-level pthread_cond_wait call.
  transitions::ensure_primitive_initialized(
      m, remote_cond, cond_flag,
      []() {
        return new condition_variable(condition_variable::cv_initialized);
      },
      "Attempting to wait on an uninitialized condition variable");

  // The mutex flag here is exact: the wrapper wrote it AFTER pthread_cond_wait
  // released the mutex (see the D-11 NOTE at the enqueue site).
  transitions::ensure_primitive_initialized(
      m, remote_mut, mutex_flag, []() { return new mutex(mutex::unlocked); },
      "Attempting to wait on a condition "
      "variable with an uninitialized mutex");

  state::objid_t const cond = m.get_model_of_object(remote_cond);
  state::objid_t const mut = m.get_model_of_object(remote_mut);
  return new transitions::condition_variable_wait(p, cond, mut);
}

model::transition *cond_signal_callback(runner_id_t p,
                                        const volatile runner_mailbox &rmb,
                                        model_to_system_map &m) {
  pthread_cond_t *remote_cond;
  memcpy_v(&remote_cond, (volatile void *)rmb.cnts, sizeof(pthread_cond_t *));

  // Payload layout [cond*:8][flag:1] (D-01): the wrapper classified the
  // condition variable in-process and wrote the flag for this transition at
  // (n_pointers=1, flag_index=0).
  const uint8_t cond_flag = mcmini_payload_read_flag(rmb.cnts, 1, 0);

  transitions::ensure_primitive_initialized(
      m, remote_cond, cond_flag,
      []() {
        return new condition_variable(condition_variable::cv_initialized);
      },
      "Attempting to signal an uninitialized condition variable");

  state::objid_t const cond = m.get_model_of_object(remote_cond);
  return new transitions::condition_variable_signal(p, cond);
}

model::transition *cond_broadcast_callback(runner_id_t p,
                                           const volatile runner_mailbox &rmb,
                                           model_to_system_map &m) {
  pthread_cond_t *remote_cond;
  memcpy_v(&remote_cond, (volatile void *)rmb.cnts, sizeof(pthread_cond_t *));

  // Payload layout [cond*:8][flag:1] (D-01): the wrapper classified the
  // condition variable in-process and wrote the flag for this transition at
  // (n_pointers=1, flag_index=0).
  const uint8_t cond_flag = mcmini_payload_read_flag(rmb.cnts, 1, 0);

  transitions::ensure_primitive_initialized(
      m, remote_cond, cond_flag,
      []() {
        return new condition_variable(condition_variable::cv_initialized);
      },
      "Attempting to broadcast on an uninitialized condition variable");

  state::objid_t const cond = m.get_model_of_object(remote_cond);
  return new transitions::condition_variable_broadcast(p, cond);
}

model::transition *cond_destroy_callback(runner_id_t p,
                                         const volatile runner_mailbox &rmb,
                                         model_to_system_map &m) {
  pthread_cond_t *remote_cond;
  memcpy_v(&remote_cond, (volatile void *)rmb.cnts, sizeof(pthread_cond_t *));

  // Payload layout [cond*:8][flag:1] (D-01): the wrapper classified the
  // condition variable in-process and wrote the flag for this transition at
  // (n_pointers=1, flag_index=0).
  const uint8_t cond_flag = mcmini_payload_read_flag(rmb.cnts, 1, 0);

  transitions::ensure_primitive_initialized(
      m, remote_cond, cond_flag,
      []() {
        return new condition_variable(condition_variable::cv_initialized);
      },
      "Attempting to destroy an uninitialized condition variable");

  state::objid_t const cond = m.get_model_of_object(remote_cond);
  return new transitions::condition_variable_destroy(p, cond);
}
