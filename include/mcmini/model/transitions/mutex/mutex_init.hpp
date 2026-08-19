#pragma once

#include "mcmini/model/objects/mutex.hpp"
#include "mcmini/model/transitions/mutex/mutex_transition.hpp"

namespace model {
namespace transitions {

struct mutex_init : public mutex_transition {
 public:
  mutex_init(runner_id_t executor, state::objid_t mutex_id)
      : mutex_transition(executor, mutex_id) {}
  ~mutex_init() = default;

  status modify(model::mutable_state& s) const override {
    using namespace model::objects;
    s.add_state_for_obj(mutex_id, new mutex(mutex::unlocked));
    return status::exists;
  }
  std::string to_string() const override {
    return "pthread_mutex_init(mutex:" + std::to_string(mutex_id) + ")";
  }
};
}  // namespace transitions
}  // namespace model
