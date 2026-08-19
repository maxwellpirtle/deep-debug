#pragma once

#include "mcmini/misc/extensions/unique_ptr.hpp"
#include "mcmini/model/visible_object_state.hpp"
#include "mcmini/misc/cond/cond_var_arbitrary_policy.hpp"
#include "mcmini/model/objects/mutex.hpp"
#include "mcmini/Thread_queue.h"
#include <memory>
#include <string>
#include <utility>
#include <vector>


namespace model {
namespace objects {

struct condition_variable : public model::visible_object_state {
 public:
  /* The four possible states for a condition variable */
  enum state {
    cv_uninitialized,
    cv_initialized,
    cv_waiting,
    cv_signaled,
    cv_transitional,
    cv_destroyed
  };

 private:
  static std::unique_ptr<ConditionVariablePolicy> make_default_policy() {
    return extensions::make_unique<ConditionVariableArbitraryPolicy>();
  }

  state current_state = state::cv_uninitialized;
  runner_id_t running_thread = 0;
  pthread_mutex_t* associated_mutex = nullptr;
  int waiting_count = 0;
  std::unique_ptr<ConditionVariablePolicy> policy = make_default_policy();

 public:
  condition_variable() = default;
  ~condition_variable() = default;
  /* Deep-copies the policy: two condition variables never share wake-group
     bookkeeping, so mutating one is unobservable through the other. */
  condition_variable(const condition_variable &other)
    : current_state(other.current_state),
      running_thread(other.running_thread),
      associated_mutex(other.associated_mutex),
      waiting_count(other.waiting_count), policy(other.policy->clone()) {}
  condition_variable &operator=(const condition_variable &) = delete;
  condition_variable(state s) : current_state(s) {}
  /* Adopts ownership of _p_. A null _p_ yields the default policy. */
  condition_variable(state s, ConditionVariablePolicy* p)
    : current_state(s),
      policy(p != nullptr ? std::unique_ptr<ConditionVariablePolicy>(p)
                          : make_default_policy()) {}
  condition_variable(state s, runner_id_t tid, pthread_mutex_t* mutex, int count)
    : current_state(s), running_thread(tid), associated_mutex(mutex), waiting_count(count){}

  /* The successor form: carries _p_, the policy a transition mutated, into
     the state it publishes. */
  condition_variable(state s, runner_id_t tid, pthread_mutex_t* mutex, int count,
    std::unique_ptr<ConditionVariablePolicy> p)
    : current_state(s), running_thread(tid), associated_mutex(mutex),
      waiting_count(count),
      policy(p != nullptr ? std::move(p) : make_default_policy()) {}

  condition_variable(state s, runner_id_t tid, pthread_mutex_t* mutex, int count,
    const std::vector<std::pair<runner_id_t, condition_variable_status>>& thread_states)
      : current_state(s), running_thread(tid), associated_mutex(mutex), waiting_count(count) {
        // Initialize the policy according to the states of the threads in waiting queue
        for (const auto& thread_with_state : thread_states) {
          if (thread_with_state.second == CV_PREWAITING || thread_with_state.second == CV_WAITING) {
            this->policy->add_waiter_with_state(thread_with_state.first,thread_with_state.second);
          }
        }
        std::vector<runner_id_t> signaled_threads;
        for (const auto& thread_with_state : thread_states) {
          if (thread_with_state.second == CV_SIGNALED) {
            signaled_threads.push_back(thread_with_state.first);
          }
        }
        if (!signaled_threads.empty()) {
          // If there are any threads that have been signaled, we should
          // add them to the wake groups in the policy.
          this->policy->add_to_wake_groups(signaled_threads);
        }
      }
  // ---- State Observation --- //
  bool operator==(const condition_variable &other) const {
    return this->current_state == other.current_state;
  }
  bool operator!=(const condition_variable &other) const {
    return this->current_state != other.current_state;
  }

  bool is_initialized() const { return this->current_state == cv_initialized ; }
  bool is_waiting() const { return this->current_state == cv_waiting ; }
  bool is_signaled() const { return this->current_state == cv_signaled ; }
  bool is_uninitialized() const { return this->current_state == cv_uninitialized ;}
  bool is_transitional() const { return this->current_state == cv_transitional;}
  bool is_destroyed() const { return this->current_state == cv_destroyed;}

  ConditionVariablePolicy* get_policy() const {return this->policy.get();}

  /* An independent copy of this state's policy, for a transition to mutate
     and hand to the successor state it publishes. Mutating the copy is
     unobservable through this state. */
  std::unique_ptr<ConditionVariablePolicy> clone_policy() const {
    return std::unique_ptr<ConditionVariablePolicy>(this->policy->clone());
  }

  void set_associated_mutex(pthread_mutex_t* mutex) {
    this->associated_mutex = mutex;
  }

  pthread_mutex_t* get_mutex() const {return this->associated_mutex;}

  bool has_waiters() const {return this->policy->has_waiters();}

  /* Spurious wake-ups are not modelled: a waiter leaves the condition
     variable only by consuming a signal or a broadcast. */
  bool waiter_can_exit(runner_id_t tid) const {
    return this->policy->thread_can_exit(tid);
  }

  std::unique_ptr<visible_object_state> clone() const override {
    return extensions::make_unique<condition_variable>(*this);
  }

  std::string to_string() const override {
    return "condition_variable(state: " + std::to_string(current_state);
    }
};
}  // namespace objects
}  // namespace model
