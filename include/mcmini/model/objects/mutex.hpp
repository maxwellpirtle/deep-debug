#pragma once

#include "mcmini/misc/extensions/unique_ptr.hpp"
#include "mcmini/model/visible_object_state.hpp"

namespace model {
namespace objects {

struct mutex : public model::visible_object_state {
 public:
  /* The four possible states for a mutex */
  enum state { uninitialized, unlocked, locked, destroyed };

 private:
  state current_state = state::uninitialized;
  // Default member initializer (CR-01): no constructor may leak an
  // indeterminate `owner` -- it participates in `operator==` and in
  // wait-enabledness checks (`is_locked_by`).
  //
  // The model deliberately holds NO `pthread_mutex_t*`: a model object is
  // identified by the `state::objid_t` the coordinator assigned it, and the
  // remote address -> objid correspondence lives exclusively in
  // `model_to_system_map`. Transitions compare object ids, never addresses.
  runner_id_t owner = 0;

 public:
  mutex() = default;
  ~mutex() = default;
  mutex(const mutex &) = default;
  mutex(state s) : current_state(s) {}
  mutex(state s, runner_id_t tid) : current_state(s), owner(tid) {}

  // ---- State Observation --- //
  bool operator==(const mutex &other) const {
    return this->current_state == other.current_state && this->owner == other.owner;

  }
  bool operator!=(const mutex &other) const {
    return this->current_state != other.current_state;
  }
  bool is_locked_by(runner_id_t tid) const { return current_state == locked && owner ==tid; }

  bool is_locked() const { return this->current_state == locked; }
  bool is_unlocked() const { return this->current_state == unlocked; }
  bool is_destroyed() const { return this->current_state == destroyed; }
  bool is_initialized() const { return this->current_state != uninitialized; }

  std::unique_ptr<visible_object_state> clone() const override {
    return extensions::make_unique<mutex>(*this);
  }
  std::string to_string() const override {
    return "mutex(" + std::to_string(current_state) + ")";
  }
};
}  // namespace objects
}  // namespace model
