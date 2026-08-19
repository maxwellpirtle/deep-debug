#pragma once

#include "mcmini/model/transition.hpp"

namespace model {
namespace transitions {

/// @brief The common base of the four semaphore operations (`sem_init`,
/// `sem_post`, `sem_wait` and `sem_destroy`), carrying the semaphore they name
/// and the relations that follow from it.
///
/// Inheritance is deliberate here in a codebase that otherwise favours
/// composition. `model::transition` is already a polymorphic hierarchy, and the
/// dispatch table registers a *pointer-to-member* (`misc/ddt.hpp`), so a free
/// function cannot be registered; a shared base is the only place one relation
/// body can serve all four leaves.
///
/// NOTE: this type is never itself registered in the dispatch table. `call_or`
/// keys on `std::type_index(typeid(*t))` -- the *dynamic* type -- against an
/// exact-match hash map with no base-class walk, so an entry filed under
/// `semaphore_transition` would never match a `sem_wait` object and would be a
/// silent no-op. Each concrete leaf is registered individually in
/// `classic_dpor.cpp`.
struct semaphore_transition : public model::transition {
 protected:
  /* The semaphore this transition operates on. Protected rather than private
   * so `to_string()` in each leaf can name it. */
  const state::objid_t sem_id;

 public:
  semaphore_transition(runner_id_t executor, state::objid_t sem_id)
      : transition(executor), sem_id(sem_id) {}
  ~semaphore_transition() = default;
  state::objid_t get_id() const { return this->sem_id; }

  // MARK: DPOR Methods

  /// @brief Two semaphore operations conflict exactly when they name the same
  /// semaphore; anything that is not a semaphore operation is independent.
  ///
  /// The second half is the cross-family claim, and it is valid because the
  /// semaphore object is read or written by these four transitions and by
  /// nothing else: a grep over every `modify` body in the tree finds
  /// `objects::semaphore` only in `sem_init`, `sem_post`, `sem_wait` and
  /// `sem_destroy` (the two remaining uses -- `mcmini.cpp` restoring a
  /// checkpointed object and `semaphore.cpp` registering one -- are not
  /// transitions and change no state along a trace). A future transition that
  /// touches a semaphore must therefore either join this family or declare a
  /// pairwise entry against it; leaving it outside both would make this method
  /// answer "independent" for a pair that is not.
  ///
  /// "Same semaphore" is decided purely on the model `state::objid_t` the two
  /// transitions carry. There is no aliasing analysis and no read of process
  /// memory: two `sem_t*` values the coordinator mapped onto one model id are
  /// one semaphore, and two model ids are two semaphores.
  bool depends(const model::transition* t) const {
    const semaphore_transition* other =
        dynamic_cast<const semaphore_transition*>(t);
    return other != nullptr && other->sem_id == this->sem_id;
  }

  /// @brief Every pair involving a semaphore operation may be co-enabled.
  ///
  /// Co-enabledness is a *static* relation over two transitions and takes no
  /// state (D-06): it asks whether there is *some* state in which both could be
  /// enabled, quantifying over states, so a `false` must be a proof that no
  /// such state exists. That is why `mutex_lock::coenabled_with(mutex_unlock)`
  /// needs nothing but the two ids -- lock requires the mutex unlocked, unlock
  /// requires it locked, and no state satisfies both.
  ///
  /// Applied honestly to semaphores there is no such proof. `sem_wait(A)` and
  /// `sem_post(A)` are both enabled in any state with count > 0; so are two
  /// `sem_wait(A)`s; and anything on distinct semaphores is trivially
  /// co-enabled. A count-based rule would hold only under "there exists a state
  /// *reachable in this program*", and deciding that is the model-checking
  /// problem itself -- the original McMini approximated it from a shadow count,
  /// which under-approximates and drops races.
  ///
  /// So this answers an explicit `true`. It is behaviourally identical to the
  /// table's fallback, but it records that the pair was analysed rather than
  /// overlooked, and it keeps the semaphore family out of the unregistered-pair
  /// alarm's output, which is exactly the distinction that alarm exists to
  /// draw.
  bool coenabled_with(const model::transition* t) const { return true; }
};

}  // namespace transitions
}  // namespace model
