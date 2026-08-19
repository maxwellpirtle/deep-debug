#pragma once

#include "mcmini/model/objects/mutex.hpp"
#include "mcmini/model/transitions/mutex/mutex_init.hpp"
#include "mcmini/model/transitions/mutex/mutex_transition.hpp"
#include "mcmini/model/transitions/mutex/mutex_unlock.hpp"

namespace model {
namespace transitions {

struct mutex_lock : public mutex_transition {
 public:
  mutex_lock(runner_id_t executor, state::objid_t mutex_id)
      : mutex_transition(executor, mutex_id) {}
  ~mutex_lock() = default;

  status modify(model::mutable_state& s) const override {
    using namespace model::objects;

    // A `mutex_lock` cannot be applied to a mutex already locked.
    const mutex* ms = s.get_state_of_object<mutex>(mutex_id);
    if (ms->is_locked()) {
      return status::disabled;
    }
    s.add_state_for_obj(mutex_id, new mutex(mutex::locked, ms->get_location(), this->executor));
    return status::exists;
  }
  std::string to_string() const override {
    return "pthread_mutex_lock(mutex:" + std::to_string(mutex_id) + ")";
  }

  // MARK: Model checking functions
  //
  // These three are two-argument entries in `classic_dpor.cpp`, so `call_or`
  // finds them in `internal_table` and never reaches the family's
  // interface-form answer for these pairs. That precedence is deliberate
  // (D-05): a specific, reviewed declaration outranks a family catch-all.
  //
  // The first two are now *redundant* -- `mutex_transition::depends` reduces to
  // the same `mutex_id` equality for a `mutex_init` or a `mutex_lock` partner,
  // so deleting them would not change an answer. They are kept anyway, and the
  // redundancy is recorded here rather than resolved (D-20): the hand-written
  // entry is the authoritative statement of the pair, and removing it would
  // make the pair depend on a catch-all continuing to agree with it.
  //
  // `coenabled_with(const mutex_unlock*)` is *not* redundant. It is the one
  // mutex pair with a proof that no state enables both -- a lock needs the
  // mutex unlocked, an unlock needs it held by the unlocking thread -- and the
  // family answers a blanket `true`, so this entry is the only place that
  // `false` comes from.
  bool depends(const mutex_init* mi) const {
    return this->mutex_id == mi->get_id();
  }
  bool depends(const mutex_lock* ml) const {
    return this->mutex_id == ml->get_id();
  }
  bool coenabled_with(const mutex_unlock* mu) const {
    return this->mutex_id != mu->get_id();
  }
};
}  // namespace transitions
}  // namespace model
