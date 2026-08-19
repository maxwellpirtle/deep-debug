#pragma once

#include <cstdint>

#include "mcmini/coordinator/model_to_system_map.hpp"
#include "mcmini/model/exception.hpp"
#include "mcmini/real_world/mailbox/mailbox_payload.h"

namespace model {
namespace transitions {

/**
 * The shared three-way decision (D-08) for a primitive named by a transition
 * callback, written once and called from every mutex and condition-variable
 * callback:
 *
 *   1. `m.contains(addr)` -- the model has already observed this primitive:
 *      return immediately and leave the modelled state untouched (D-09). The
 *      flag byte is never consulted for an observed object; whatever the
 *      model believes about it (locked, destroyed, ...) stands.
 *   2. flag == `MCMINI_PRIMITIVE_STATIC_INIT` -- the wrapper's in-process
 *      memcmp found the primitive byte-equal to its `PTHREAD_*_INITIALIZER`
 *      pattern: static initialization is legal initialization, so lazily
 *      register the object via `make_state()` in its freshly-initialized
 *      state (the existing single-arg `observe_object` form, D-09).
 *   3. otherwise -- the primitive is unobserved AND its bytes do not match
 *      the static initializer: the operation acts on an uninitialized
 *      primitive, which is undefined behavior. Throw, naming the operation.
 *
 * NOTE: this guard must precede any query of model state below. An address
 * the model has never seen resolves to `model::invalid_objid`, and indexing
 * the model with that is an out-of-range lookup no `verify_using` catch
 * clause handles.
 *
 * @param m the model-to-system correspondence for the current translation.
 * @param addr the remote address of the primitive the operation names.
 * @param static_init_flag the flag byte the wrapper wrote for THIS
 *        transition, exactly one of `MCMINI_PRIMITIVE_STATIC_INIT` /
 *        `MCMINI_PRIMITIVE_NOT_STATIC_INIT` (D-03).
 * @param make_state factory (e.g. a C++11 lambda) returning a new
 *        `visible_object_state *` representing the freshly-initialized
 *        primitive; invoked only in case 2.
 * @param ub_message the operation-naming message for case 3, passed through
 *        unchanged to `undefined_behavior_exception` (D-10).
 */
template <typename StateFactory>
void ensure_primitive_initialized(model_to_system_map &m,
                                  real_world::remote_address<void> addr,
                                  uint8_t static_init_flag,
                                  StateFactory make_state,
                                  const char *ub_message) {
  if (m.contains(addr)) return;
  if (static_init_flag == MCMINI_PRIMITIVE_STATIC_INIT) {
    m.observe_object(addr, make_state());
    return;
  }
  throw undefined_behavior_exception(ub_message);
}

}  // namespace transitions
}  // namespace model
