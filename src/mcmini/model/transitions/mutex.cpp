#include "mcmini/mem.h"
#include "mcmini/model/exception.hpp"
#include "mcmini/model/transitions/mutex/callbacks.hpp"
#include "mcmini/model/transitions/static_init_registration.hpp"
#include "mcmini/real_world/mailbox/mailbox_payload.h"

using namespace model;
using namespace objects;

model::transition *mutex_init_callback(runner_id_t p,
                                       const volatile runner_mailbox &rmb,
                                       model_to_system_map &m) {
  // Fetch the remote object
  pthread_mutex_t *remote_mut;
  memcpy_v(&remote_mut, (volatile void *)rmb.cnts, sizeof(pthread_mutex_t *));

  // Locate the corresponding model of this object
  if (!m.contains(remote_mut))
    m.observe_object(remote_mut, new mutex(mutex::state::uninitialized));

  state::objid_t const mut = m.get_model_of_object(remote_mut);
  return new transitions::mutex_init(p, mut);
}

model::transition *mutex_lock_callback(runner_id_t p,
                                       const volatile runner_mailbox &rmb,
                                       model_to_system_map &m) {
  pthread_mutex_t *remote_mut;
  memcpy_v(&remote_mut, (volatile void *)rmb.cnts, sizeof(pthread_mutex_t *));
  // Payload layout [mutex*:8][flag:1] (D-01): the wrapper classified the
  // mutex against PTHREAD_MUTEX_INITIALIZER in-process and wrote the flag
  // for this transition at (n_pointers=1, flag_index=0).
  const uint8_t static_init_flag = mcmini_payload_read_flag(rmb.cnts, 1, 0);

  transitions::ensure_primitive_initialized(
      m, remote_mut, static_init_flag,
      []() { return new mutex(mutex::unlocked); },
      "Attempting to lock an uninitialized mutex");

  state::objid_t const mut = m.get_model_of_object(remote_mut);
  return new transitions::mutex_lock(p, mut);
}

model::transition *mutex_unlock_callback(runner_id_t p,
                                         const volatile runner_mailbox &rmb,
                                         model_to_system_map &m) {
  pthread_mutex_t *remote_mut;
  memcpy_v(&remote_mut, (volatile void *)rmb.cnts, sizeof(pthread_mutex_t *));
  const uint8_t static_init_flag = mcmini_payload_read_flag(rmb.cnts, 1, 0);

  transitions::ensure_primitive_initialized(
      m, remote_mut, static_init_flag,
      []() { return new mutex(mutex::unlocked); },
      "Attempting to unlock an uninitialized mutex");

  state::objid_t const mut = m.get_model_of_object(remote_mut);
  return new transitions::mutex_unlock(p, mut);
}
