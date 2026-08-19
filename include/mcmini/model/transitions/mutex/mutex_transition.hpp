#pragma once

#include "mcmini/model/transition.hpp"

namespace model {
namespace transitions {

/// @brief The common base of the three mutex operations (`mutex_init`,
/// `mutex_lock` and `mutex_unlock`), carrying the mutex they name and the
/// relations that follow from it.
///
/// Inheritance is deliberate here in a codebase that otherwise favours
/// composition, for the same reason it is in `semaphore_transition`:
/// `model::transition` is already a polymorphic hierarchy, and the dispatch
/// table registers a *pointer-to-member* (`misc/ddt.hpp`), so a free function
/// cannot be registered; a shared base is the only place one relation body can
/// serve all three leaves.
///
/// NOTE: this type is never itself registered in the dispatch table. `call_or`
/// keys on `std::type_index(typeid(*t))` -- the *dynamic* type -- against an
/// exact-match hash map with no base-class walk, so an entry filed under
/// `mutex_transition` would never match a `mutex_unlock` object and would be a
/// silent no-op. Each concrete leaf is registered individually in
/// `classic_dpor.cpp`.
struct mutex_transition : public model::transition {
 protected:
  /* The mutex this transition operates on. Protected rather than private so
   * `to_string()` in each leaf can name it. */
  const state::objid_t mutex_id;

 public:
  mutex_transition(runner_id_t executor, state::objid_t mutex_id)
      : transition(executor), mutex_id(mutex_id) {}
  ~mutex_transition() = default;
  state::objid_t get_id() const { return this->mutex_id; }

  // MARK: DPOR Methods

  /// @brief Two mutex operations conflict exactly when they name the same
  /// mutex; anything that is not a mutex operation is independent.
  ///
  /// The second half is the cross-family claim, and unlike the semaphore
  /// family's it is *not* true because nothing outside this family touches the
  /// object. Exactly two non-mutex transitions read and write a mutex --
  /// `condition_variable_wait` and `condition_variable_enqueue_thread`,
  /// established by a grep over every `modify` body in the tree (the only other
  /// use, `mcmini.cpp` rebuilding a checkpointed `objects::mutex`, is not a
  /// transition and changes no state along a trace). Both are *disabled* by the
  /// mutex's state and both change it, so under Flanagan-Godefroid Definition 1
  /// -- independent transitions can neither enable nor disable one another --
  /// each is dependent with every operation on the same mutex. Answering
  /// "independent" for those pairs would be unsound.
  ///
  /// What makes the blanket `false` below valid is that this method is never
  /// the voice on them. All six pairs formed from the three mutex leaves and
  /// those two condition-variable transitions are declared as two-argument
  /// entries in `classic_dpor::default_dependencies()`, and `call_or` consults
  /// `internal_table` -- where two-argument entries live -- *before* the
  /// interface table this family is registered in. A hand-written pair
  /// therefore wins outright.
  ///
  /// A future transition that reads or writes a mutex must consequently either
  /// join this family or declare a pairwise entry against each of its leaves.
  /// Leaving it outside both would silently route it here, and this `false`
  /// would become the unsound answer described above.
  ///
  /// "Same mutex" is decided purely on the model `state::objid_t` the two
  /// transitions carry. There is no aliasing analysis and no read of process
  /// memory: two `pthread_mutex_t*` values the coordinator mapped onto one
  /// model id are one mutex, and two model ids are two mutexes.
  bool depends(const model::transition* t) const {
    const mutex_transition* other = dynamic_cast<const mutex_transition*>(t);
    return other != nullptr && other->mutex_id == this->mutex_id;
  }

  // MARK: Why this family declares no co-enabledness relation
  //
  // Co-enabledness is a *static* relation over two transitions and takes no
  // state (D-06): it asks whether there is *some* state in which both could be
  // enabled, quantifying over states, so a `false` must be a proof that no such
  // state exists. Do not add a `state` parameter to any such signature; a
  // per-state check answers a different, weaker question.
  //
  // Three mutex-related pairs do have such a proof -- `mutex_lock` against
  // `mutex_unlock` on one mutex (lock needs it unlocked, unlock needs it held
  // by the unlocking thread), and `condition_variable_enqueue_thread` against
  // each of `mutex_lock` and `mutex_unlock` on one mutex. All three are
  // declared *pairwise*, and pairwise entries live in `internal_table`, which
  // `call_or` consults first. This family would therefore have nothing left to
  // claim but a blanket `true`.
  //
  // A blanket `true` looks free -- it is the table's own fallback value -- and
  // it is not. `call_or`'s two-sided rule (plan 02-01) asks *both* whole-
  // interface entries when both types declare one, and returns the fallback if
  // either answers it. `thread_create::coenabled_with` and
  // `thread_join::coenabled_with` answer a *proven* `false` for any transition
  // executed by the thread being created or joined -- a created thread cannot
  // act before it exists, and a joined thread cannot act after it has exited.
  // Registering a blanket `true` here vetoes both proofs, because a fallback-
  // valued answer is indistinguishable from a claim.
  //
  // That is not a soundness loss but it is a large reduction loss, measured on
  // this plan's own benchmark: `mutex-bug` 38 -> 4827 traces and `mutex-clean`
  // 34 -> 2982 at `--threads=3` with the registration present. The same
  // registration on the semaphore family cost `sem-bug` 21 -> 99. So the family
  // registers `depends` only, and mutex pairs reach the *identical* `true`
  // through the fallback. The analysis D-07 wanted recorded lives here, in the
  // header, rather than in an entry that suppresses other families' proofs.
};

}  // namespace transitions
}  // namespace model
