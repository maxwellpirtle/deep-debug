/// Unit tests for the DPOR dependence and co-enabledness relations.
///
/// The relations are reached through `classic_dpor::default_dependencies()` and
/// `classic_dpor::default_coenabledness()`, which are public statics, and
/// through `double_dispatch_member_function_table::call_or`, which is public.
/// `classic_dpor::are_dependent` / `are_coenabled` are private; the only thing
/// they add on top of `call_or` is a same-executor short circuit, which is
/// trivially symmetric and which the roster below sidesteps by giving every
/// sample transition a distinct executor.
///
/// Assertions are hand-rolled rather than `assert()`: the Release build defines
/// `NDEBUG` and would compile every `assert()` away, leaving a test that passes
/// vacuously.

#include <cstddef>
#include <iostream>
#include <memory>
#include <string>
#include <vector>

#include "mcmini/model/transitions/condition_variables/condition_variable_brdcast.hpp"
#include "mcmini/model/transitions/condition_variables/condition_variable_enqueue_thread.hpp"
#include "mcmini/model/transitions/condition_variables/condition_variables_destroy.hpp"
#include "mcmini/model/transitions/condition_variables/condition_variables_init.hpp"
#include "mcmini/model/transitions/condition_variables/condition_variables_signal.hpp"
#include "mcmini/model/transitions/condition_variables/condition_variables_wait.hpp"
#include "mcmini/model/transitions/mutex/mutex_init.hpp"
#include "mcmini/model/transitions/mutex/mutex_lock.hpp"
#include "mcmini/model/transitions/mutex/mutex_unlock.hpp"
#include "mcmini/model/transitions/process/abort.hpp"
#include "mcmini/model/transitions/process/exit.hpp"
#include "mcmini/model/transitions/semaphore/sem_destroy.hpp"
#include "mcmini/model/transitions/semaphore/sem_init.hpp"
#include "mcmini/model/transitions/semaphore/sem_post.hpp"
#include "mcmini/model/transitions/semaphore/sem_wait.hpp"
#include "mcmini/model/transitions/thread/thread_create.hpp"
#include "mcmini/model/transitions/thread/thread_exit.hpp"
#include "mcmini/model/transitions/thread/thread_join.hpp"
#include "mcmini/model/transitions/thread/thread_start.hpp"
#include "mcmini/model_checking/algorithms/classic_dpor.hpp"

static int g_failures = 0;

#define CHECK(cond, msg)                                                 \
  do {                                                                   \
    if (!(cond)) {                                                       \
      ++g_failures;                                                      \
      std::cerr << "FAIL " << __FILE__ << ":" << __LINE__ << ": " << msg \
                << std::endl;                                            \
    }                                                                    \
  } while (0)

namespace {

using model_checking::classic_dpor;

// Qualified rather than `using namespace`: `sem_init`, `sem_post`, `sem_wait`
// and `sem_destroy` name POSIX functions declared by <semaphore.h>, which the
// model headers pull in transitively.
namespace mt = model::transitions;

using transition_ptr = std::unique_ptr<model::transition>;
using objid_t = model::state::objid_t;

template <typename T>
transition_ptr own(T *t) {
  return transition_ptr(t);
}

// `thread_create` and `thread_join` answer on their *target*, so the roster
// names a real member: creation targets the roster's `thread_start` and join
// targets the roster's `thread_exit`. These are precisely the two pairs where
// both types carry an interface-form entry and the answers disagree.
const runner_id_t RID_THREAD_START = 10;
const runner_id_t RID_THREAD_EXIT = 11;

/// @brief One instance of every concrete transition type, each with a distinct
/// executor.
///
/// @param distinct_ids when false every visible object carries the same id, so
/// the id-equality relations answer "same object"; when true every object is
/// distinct, so those same relations answer "different object". Sweeping both
/// exercises each relation on both sides of its comparison.
std::vector<transition_ptr> make_roster(bool distinct_ids) {
  const auto oid = [distinct_ids](int slot) -> objid_t {
    return static_cast<objid_t>(distinct_ids ? slot : 1);
  };

  std::vector<transition_ptr> r;
  r.push_back(own(new mt::mutex_init(1, oid(1))));
  r.push_back(own(new mt::mutex_lock(2, oid(2))));
  r.push_back(own(new mt::mutex_unlock(3, oid(3))));
  r.push_back(own(new mt::sem_init(4, oid(4))));
  r.push_back(own(new mt::sem_post(5, oid(5))));
  r.push_back(own(new mt::sem_wait(6, oid(6))));
  r.push_back(own(new mt::sem_destroy(7, oid(7))));
  r.push_back(own(new mt::thread_create(8, RID_THREAD_START)));
  r.push_back(own(new mt::thread_join(9, RID_THREAD_EXIT)));
  r.push_back(own(new mt::thread_start(RID_THREAD_START)));
  r.push_back(own(new mt::thread_exit(RID_THREAD_EXIT)));
  r.push_back(own(new mt::process_exit(12)));
  r.push_back(own(new mt::process_abort(13)));
  r.push_back(own(new mt::condition_variable_init(14, oid(14))));
  r.push_back(
      own(new mt::condition_variable_enqueue_thread(15, oid(15), oid(115))));
  r.push_back(own(new mt::condition_variable_wait(16, oid(16), oid(116))));
  r.push_back(own(new mt::condition_variable_signal(17, oid(17))));
  r.push_back(own(new mt::condition_variable_broadcast(18, oid(18))));
  r.push_back(own(new mt::condition_variable_destroy(19, oid(19))));
  return r;
}

void check_distinct_executors(const std::vector<transition_ptr> &roster) {
  for (size_t i = 0; i < roster.size(); ++i) {
    for (size_t j = i + 1; j < roster.size(); ++j) {
      CHECK(roster[i]->get_executor() != roster[j]->get_executor(),
            "roster entries " << roster[i]->to_string() << " and "
                              << roster[j]->to_string() << " share executor "
                              << roster[i]->get_executor());
    }
  }
}

/// Both relations must be functions of the *unordered* pair: every call site
/// picks its own argument order (`accumulate_max_clock_vector_against` asks
/// earlier-then-later, the race test asks later-then-earlier), so a relation
/// that is not symmetric answers a different question at each one.
void sweep_symmetry(const char *label,
                    const std::vector<transition_ptr> &roster) {
  const classic_dpor::dependency_relation_type dr =
      classic_dpor::default_dependencies();
  const classic_dpor::coenabled_relation_type cr =
      classic_dpor::default_coenabledness();

  for (size_t i = 0; i < roster.size(); ++i) {
    for (size_t j = 0; j < roster.size(); ++j) {
      const model::transition *a = roster[i].get();
      const model::transition *b = roster[j].get();
      CHECK(dr.call_or(true, a, b) == dr.call_or(true, b, a),
            label << ": dependence is asymmetric for (" << a->to_string()
                  << ", " << b->to_string() << ")");
      CHECK(cr.call_or(true, a, b) == cr.call_or(true, b, a),
            label << ": co-enabledness is asymmetric for (" << a->to_string()
                  << ", " << b->to_string() << ")");
    }
  }
}

/// The two pairs where both types carry an interface-form entry and the two
/// entries disagree. Before the two-sided resolution rule, whichever transition
/// was passed first decided the answer.
void check_two_sided_collisions() {
  const classic_dpor::dependency_relation_type dr =
      classic_dpor::default_dependencies();

  const mt::thread_create creates(8, RID_THREAD_START);
  const mt::thread_start starts(RID_THREAD_START);
  const mt::thread_join joins(9, RID_THREAD_EXIT);
  const mt::thread_exit exits(RID_THREAD_EXIT);

  // `thread_create::depends` claims the pair, `thread_start::depends` denies
  // it. Disagreement resolves to the fallback, "dependent" — the direction
  // that cannot lose a bug.
  CHECK(dr.call_or(true, &creates, &starts),
        "a thread's creation and its start must be dependent");
  CHECK(dr.call_or(true, &starts, &creates),
        "a thread's start and its creation must be dependent");
  CHECK(dr.call_or(true, &joins, &exits),
        "a thread's join and its exit must be dependent");
  CHECK(dr.call_or(true, &exits, &joins),
        "a thread's exit and its join must be dependent");

  // The rule must not collapse into "everything is dependent": a creation and
  // an unrelated thread's start still agree that they commute.
  const mt::thread_start unrelated_start(RID_THREAD_EXIT);
  CHECK(!dr.call_or(true, &creates, &unrelated_start),
        "a creation and an unrelated thread's start must be independent");
  CHECK(!dr.call_or(true, &unrelated_start, &creates),
        "an unrelated thread's start and a creation must be independent");
}

/// A pair no relation answers must say so, exactly once per unordered pair.
void check_unregistered_pair_alarm() {
  classic_dpor::dependency_relation_type dr =
      classic_dpor::default_dependencies();

  std::vector<std::string> reported;
  dr.set_unregistered_pair_observer(
      [&reported](const std::type_info &t1, const std::type_info &t2) {
        reported.push_back(std::string(t1.name()) + " x " + t2.name());
      });

  // Two condition variables. `condition_variable_init` carries no relation at
  // all and is deliberately left that way, so the pair reaches the fallback.
  const mt::condition_variable_init init_a(1, 100);
  const mt::condition_variable_init init_b(2, 200);
  dr.call_or(true, &init_a, &init_b);
  dr.call_or(true, &init_b, &init_a);
  CHECK(reported.size() == 1,
        "an unanswered pair must be reported once across both argument "
        "orders, saw "
            << reported.size());

  // The same, for two *different* unanswered types: this is what proves the
  // key is normalised rather than merely identical in both orders.
  // `condition_variable_signal` has no entry against `condition_variable_init`
  // and, per D-14, the residual CV x CV pairs are deliberately left for the
  // alarm to report rather than closed in this phase.
  reported.clear();
  const mt::condition_variable_signal signals(3, 300);
  dr.call_or(true, &init_a, &signals);
  dr.call_or(true, &signals, &init_a);
  CHECK(reported.size() == 1,
        "an unanswered heterogeneous pair must be reported once across both "
        "argument orders, saw "
            << reported.size());

  // ... and a pair that *is* answered must stay silent. `process_exit` and
  // `process_abort` are registered, so no run opens with the same two alarms.
  reported.clear();
  const mt::process_exit exits(4);
  const mt::process_abort aborts(5);
  const mt::mutex_lock locks(6, 400);
  dr.call_or(true, &exits, &locks);
  dr.call_or(true, &locks, &exits);
  dr.call_or(true, &aborts, &locks);
  dr.call_or(true, &locks, &aborts);
  CHECK(reported.empty(),
        "a registered pair must not be reported, saw " << reported.size());
}

/// `process_exit` and `process_abort` write no state and are never disabled.
void check_process_transitions() {
  const classic_dpor::dependency_relation_type dr =
      classic_dpor::default_dependencies();
  const classic_dpor::coenabled_relation_type cr =
      classic_dpor::default_coenabledness();

  const mt::process_exit exits(4);
  const mt::process_abort aborts(5);
  const mt::mutex_lock locks(6, 400);

  CHECK(!dr.call_or(true, &exits, &locks),
        "process exit must be independent of a mutex lock");
  CHECK(!dr.call_or(true, &locks, &exits),
        "a mutex lock must be independent of process exit");
  CHECK(!dr.call_or(true, &aborts, &locks),
        "process abort must be independent of a mutex lock");
  CHECK(!dr.call_or(true, &locks, &aborts),
        "a mutex lock must be independent of process abort");

  CHECK(cr.call_or(true, &exits, &locks),
        "process exit must be co-enabled with a mutex lock");
  CHECK(cr.call_or(true, &locks, &exits),
        "a mutex lock must be co-enabled with process exit");
  CHECK(cr.call_or(true, &aborts, &locks),
        "process abort must be co-enabled with a mutex lock");
  CHECK(cr.call_or(true, &locks, &aborts),
        "a mutex lock must be co-enabled with process abort");
}

/// A relation must give the same answer whichever way round it is asked.
void expect_both_orders(const classic_dpor::dependency_relation_type &table,
                        const model::transition &a, const model::transition &b,
                        bool expected, const char *what) {
  CHECK(table.call_or(true, &a, &b) == expected,
        what << ": expected " << expected << " asked (first, second)");
  CHECK(table.call_or(true, &b, &a) == expected,
        what << ": expected " << expected << " asked (second, first)");
}

/// The two condition-variable transitions whose `modify` touches a mutex must
/// be answered pairwise against every mutex operation. The distinct-mutex half
/// of each case is the load-bearing one: a pair falling through to the
/// conservative fallback would answer "dependent" for both mutexes alike.
void check_cv_x_mutex() {
  const classic_dpor::dependency_relation_type dr =
      classic_dpor::default_dependencies();
  const classic_dpor::coenabled_relation_type cr =
      classic_dpor::default_coenabledness();

  const objid_t the_mutex = 1;
  const objid_t another_mutex = 2;
  const objid_t the_cv = 3;

  const mt::condition_variable_wait waits(1, the_cv, the_mutex);
  const mt::condition_variable_enqueue_thread enqueues(2, the_cv, the_mutex);

  const mt::mutex_init inits(3, the_mutex);
  const mt::mutex_lock locks(4, the_mutex);
  const mt::mutex_unlock unlocks(5, the_mutex);
  const mt::mutex_init inits_other(6, another_mutex);
  const mt::mutex_lock locks_other(7, another_mutex);
  const mt::mutex_unlock unlocks_other(8, another_mutex);

  expect_both_orders(dr, waits, inits, true, "cond wait x mutex init, same");
  expect_both_orders(dr, waits, locks, true, "cond wait x mutex lock, same");
  expect_both_orders(dr, waits, unlocks, true,
                     "cond wait x mutex unlock, same");
  expect_both_orders(dr, waits, inits_other, false,
                     "cond wait x mutex init, other mutex");
  expect_both_orders(dr, waits, locks_other, false,
                     "cond wait x mutex lock, other mutex");
  expect_both_orders(dr, waits, unlocks_other, false,
                     "cond wait x mutex unlock, other mutex");

  expect_both_orders(dr, enqueues, inits, true,
                     "cv enqueue x mutex init, same");
  expect_both_orders(dr, enqueues, locks, true,
                     "cv enqueue x mutex lock, same");
  expect_both_orders(dr, enqueues, unlocks, true,
                     "cv enqueue x mutex unlock, same");
  expect_both_orders(dr, enqueues, inits_other, false,
                     "cv enqueue x mutex init, other mutex");
  expect_both_orders(dr, enqueues, locks_other, false,
                     "cv enqueue x mutex lock, other mutex");
  expect_both_orders(dr, enqueues, unlocks_other, false,
                     "cv enqueue x mutex unlock, other mutex");

  // Enqueueing holds the mutex; locking needs it free and unlocking needs it
  // held by the unlocking thread. Different executors, one mutex: never both.
  expect_both_orders(cr, enqueues, locks, false,
                     "cv enqueue x mutex lock co-enabledness, same mutex");
  expect_both_orders(cr, enqueues, unlocks, false,
                     "cv enqueue x mutex unlock co-enabledness, same mutex");
  expect_both_orders(cr, enqueues, locks_other, true,
                     "cv enqueue x mutex lock co-enabledness, other mutex");
  expect_both_orders(cr, enqueues, unlocks_other, true,
                     "cv enqueue x mutex unlock co-enabledness, other mutex");
}

/// `condition_variable_broadcast` and `condition_variable_destroy` carry
/// relation methods that were never reachable because they were never
/// registered.
void check_broadcast_and_destroy() {
  const classic_dpor::dependency_relation_type dr =
      classic_dpor::default_dependencies();
  const classic_dpor::coenabled_relation_type cr =
      classic_dpor::default_coenabledness();

  const objid_t the_cv = 1;
  const objid_t another_cv = 2;
  const objid_t the_mutex = 3;

  const mt::condition_variable_broadcast broadcasts(1, the_cv);
  const mt::condition_variable_destroy destroys(2, the_cv);
  const mt::condition_variable_wait waits(3, the_cv, the_mutex);
  const mt::condition_variable_signal signals(4, the_cv);

  const mt::condition_variable_broadcast broadcasts_other(5, another_cv);
  const mt::condition_variable_destroy destroys_other(6, another_cv);
  const mt::condition_variable_wait waits_other(7, another_cv, the_mutex);
  const mt::condition_variable_signal signals_other(8, another_cv);

  expect_both_orders(dr, broadcasts, waits, true, "broadcast x wait, same cv");
  expect_both_orders(dr, broadcasts, signals, true,
                     "broadcast x signal, same cv");
  expect_both_orders(dr, broadcasts, destroys, true,
                     "broadcast x destroy, same cv");
  expect_both_orders(dr, destroys, waits, true, "destroy x wait, same cv");
  expect_both_orders(dr, destroys, signals, true, "destroy x signal, same cv");

  expect_both_orders(dr, broadcasts, waits_other, false,
                     "broadcast x wait, other cv");
  expect_both_orders(dr, broadcasts, signals_other, false,
                     "broadcast x signal, other cv");
  expect_both_orders(dr, broadcasts, destroys_other, false,
                     "broadcast x destroy, other cv");
  expect_both_orders(dr, destroys, waits_other, false,
                     "destroy x wait, other cv");
  expect_both_orders(dr, destroys, signals_other, false,
                     "destroy x signal, other cv");

  expect_both_orders(cr, broadcasts, destroys, false,
                     "broadcast x destroy co-enabledness, same cv");
  expect_both_orders(cr, broadcasts_other, destroys, true,
                     "broadcast x destroy co-enabledness, other cv");
}

// MARK: The semaphore family

const objid_t THE_SEM = 100;
const objid_t ANOTHER_SEM = 200;

/// @brief One of each semaphore leaf, all naming `sem`, on four consecutive
/// executors starting at `first_executor`.
///
/// Two rosters on the *same* semaphore rather than one roster compared against
/// itself: the diagonal of the sweep (`sem_wait` x `sem_wait`) needs two
/// distinct objects, and on the distinct-id half it needs two objects naming
/// two different semaphores.
std::vector<transition_ptr> make_semaphore_roster(runner_id_t first_executor,
                                                  objid_t sem) {
  std::vector<transition_ptr> r;
  r.push_back(own(new mt::sem_init(first_executor + 0, sem)));
  r.push_back(own(new mt::sem_post(first_executor + 1, sem)));
  r.push_back(own(new mt::sem_wait(first_executor + 2, sem)));
  r.push_back(own(new mt::sem_destroy(first_executor + 3, sem)));
  return r;
}

/// All sixteen ordered pairs of semaphore leaves, on one semaphore and on two.
///
/// The distinct-semaphore half is the load-bearing one. A pair that fell
/// through to the conservative fallback would answer "dependent" for both
/// halves alike, so only the distinct-id assertions tell "registered and
/// resolved" apart from "never registered" -- which is exactly the silent
/// no-op a family-base registration would have produced.
void check_semaphore_x_semaphore() {
  const classic_dpor::dependency_relation_type dr =
      classic_dpor::default_dependencies();
  const classic_dpor::coenabled_relation_type cr =
      classic_dpor::default_coenabledness();

  const std::vector<transition_ptr> a = make_semaphore_roster(1, THE_SEM);
  const std::vector<transition_ptr> b = make_semaphore_roster(5, THE_SEM);
  const std::vector<transition_ptr> c = make_semaphore_roster(9, ANOTHER_SEM);

  for (size_t i = 0; i < a.size(); ++i) {
    for (size_t j = 0; j < b.size(); ++j) {
      expect_both_orders(dr, *a[i], *b[j], true,
                         "semaphore x semaphore, one semaphore");
      expect_both_orders(dr, *a[i], *c[j], false,
                         "semaphore x semaphore, two semaphores");

      // D-07: no semaphore pair has a state-independent proof that both can
      // never be enabled, so every pair is co-enabled on one semaphore and on
      // two alike.
      expect_both_orders(cr, *a[i], *b[j], true,
                         "semaphore co-enabledness, one semaphore");
      expect_both_orders(cr, *a[i], *c[j], true,
                         "semaphore co-enabledness, two semaphores");
    }
  }
}

/// The cross-family half of the claim: no transition outside the semaphore
/// family reads or writes a semaphore, so none of them conflicts with one.
///
/// Each partner is tested twice, once carrying an id numerically equal to the
/// semaphore's and once not. Ids are drawn from a single `objid_t` space, so
/// numeric equality across families is possible and must not be mistaken for
/// "same object" -- the relation distinguishes them by `dynamic_cast`, not by
/// id.
///
/// The mutex partners have no interface entry until plan 02-03 lands, so today
/// these pairs resolve through the semaphore side alone; afterwards they become
/// two-sided collisions where the mutex family also answers "not a mutex
/// operation, therefore independent". The expected answer is the same in both
/// worlds, which is why it is written as a plain expectation rather than a
/// conditional one.
void check_semaphore_x_other_families() {
  const classic_dpor::dependency_relation_type dr =
      classic_dpor::default_dependencies();

  const std::vector<transition_ptr> sems = make_semaphore_roster(1, THE_SEM);

  // `thread_create` answers on its *target*, so the target is a runner no
  // semaphore transition executes on. A creation of the very thread that then
  // performs a semaphore operation genuinely is dependent, and that is a claim
  // about runners, not about semaphores.
  const runner_id_t RID_UNRELATED = 90;

  std::vector<transition_ptr> partners;
  partners.push_back(own(new mt::mutex_init(20, THE_SEM)));
  partners.push_back(own(new mt::mutex_init(21, ANOTHER_SEM)));
  partners.push_back(own(new mt::mutex_lock(22, THE_SEM)));
  partners.push_back(own(new mt::mutex_lock(23, ANOTHER_SEM)));
  partners.push_back(own(new mt::mutex_unlock(24, THE_SEM)));
  partners.push_back(own(new mt::mutex_unlock(25, ANOTHER_SEM)));
  partners.push_back(own(new mt::thread_create(26, RID_UNRELATED)));
  partners.push_back(own(new mt::thread_start(RID_UNRELATED)));
  partners.push_back(own(new mt::condition_variable_init(27, THE_SEM)));
  partners.push_back(own(new mt::condition_variable_init(28, ANOTHER_SEM)));
  partners.push_back(own(new mt::condition_variable_signal(29, THE_SEM)));
  partners.push_back(own(new mt::condition_variable_signal(30, ANOTHER_SEM)));

  for (size_t i = 0; i < sems.size(); ++i) {
    for (size_t j = 0; j < partners.size(); ++j) {
      expect_both_orders(dr, *sems[i], *partners[j], false,
                         "semaphore x non-semaphore");
    }
  }
}

// MARK: The mutex family

const objid_t THE_MUTEX = 300;
const objid_t ANOTHER_MUTEX = 400;

/// @brief One of each mutex leaf, all naming `mutex`, on three consecutive
/// executors starting at `first_executor`.
///
/// Two rosters on the *same* mutex rather than one roster compared against
/// itself: the diagonal of the sweep (`mutex_unlock` x `mutex_unlock`) needs
/// two distinct objects, and on the distinct-id half it needs two objects
/// naming two different mutexes.
std::vector<transition_ptr> make_mutex_roster(runner_id_t first_executor,
                                              objid_t mutex) {
  std::vector<transition_ptr> r;
  r.push_back(own(new mt::mutex_init(first_executor + 0, mutex)));
  r.push_back(own(new mt::mutex_lock(first_executor + 1, mutex)));
  r.push_back(own(new mt::mutex_unlock(first_executor + 2, mutex)));
  return r;
}

/// All nine ordered pairs of mutex leaves, on one mutex and on two.
///
/// The distinct-mutex half is the load-bearing one. A pair that fell through to
/// the conservative fallback would answer "dependent" for both halves alike, so
/// only the distinct-id assertions tell "registered and resolved" apart from
/// "never registered" -- which is exactly the silent no-op a family-base
/// registration would have produced. `mutex_unlock` x `mutex_unlock` on two
/// mutexes is the assertion DEPS-03 names most directly: before this family,
/// `mutex_unlock` carried no relation at all.
void check_mutex_x_mutex() {
  const classic_dpor::dependency_relation_type dr =
      classic_dpor::default_dependencies();

  const std::vector<transition_ptr> a = make_mutex_roster(1, THE_MUTEX);
  const std::vector<transition_ptr> b = make_mutex_roster(4, THE_MUTEX);
  const std::vector<transition_ptr> c = make_mutex_roster(7, ANOTHER_MUTEX);

  for (size_t i = 0; i < a.size(); ++i) {
    for (size_t j = 0; j < b.size(); ++j) {
      expect_both_orders(dr, *a[i], *b[j], true, "mutex x mutex, one mutex");
      expect_both_orders(dr, *a[i], *c[j], false, "mutex x mutex, two mutexes");
    }
  }

  // Named out of the sweep because it is the requirement itself, and a reader
  // looking for DEPS-03 should find it spelled out rather than implied by a
  // loop bound.
  const mt::mutex_unlock unlocks_one(20, THE_MUTEX);
  const mt::mutex_unlock unlocks_another(21, ANOTHER_MUTEX);
  expect_both_orders(dr, unlocks_one, unlocks_another, false,
                     "DEPS-03: unlocks of two distinct mutexes are independent");
}

/// The hand-written pairwise entries must keep winning over the family.
///
/// `condition_variable_wait` and `condition_variable_enqueue_thread` read and
/// write the mutex object, so the family's "not a mutex operation, therefore
/// independent" would be *unsound* for them. `call_or` consults `internal_table`
/// -- where two-argument entries live -- before the interface table the family
/// is registered in, and these six assertions are the mechanical guard on that
/// ordering. If the family had taken the pairs over, every one would read
/// "independent".
void check_cv_x_mutex_pairwise_still_wins() {
  const classic_dpor::dependency_relation_type dr =
      classic_dpor::default_dependencies();

  const objid_t the_mutex = 1;
  const objid_t the_cv = 2;

  const mt::condition_variable_wait waits(1, the_cv, the_mutex);
  const mt::condition_variable_enqueue_thread enqueues(2, the_cv, the_mutex);

  const std::vector<transition_ptr> mutexes = make_mutex_roster(3, the_mutex);

  for (size_t i = 0; i < mutexes.size(); ++i) {
    expect_both_orders(dr, waits, *mutexes[i], true,
                       "the pairwise cond-wait x mutex entry must still win "
                       "over the mutex family");
    expect_both_orders(dr, enqueues, *mutexes[i], true,
                       "the pairwise cv-enqueue x mutex entry must still win "
                       "over the mutex family");
  }
}

/// The cross-family half: no transition outside the mutex family other than the
/// two guarded above reads or writes a mutex, so none of them conflicts with
/// one.
///
/// Each partner is tested twice, once carrying an id numerically equal to the
/// mutex's and once not. Ids are drawn from a single `objid_t` space, so
/// numeric equality across families is possible and must not be mistaken for
/// "same object" -- the relation distinguishes them by `dynamic_cast`, not by
/// id.
void check_mutex_x_other_families() {
  const classic_dpor::dependency_relation_type dr =
      classic_dpor::default_dependencies();

  const std::vector<transition_ptr> mutexes = make_mutex_roster(1, THE_MUTEX);

  // `thread_start` and `thread_exit` answer on their own executor, and
  // `thread_create` / `thread_join` on their target, so the roster below uses
  // runners no mutex transition executes on. A creation of the very thread that
  // then locks a mutex genuinely is dependent, and that is a claim about
  // runners rather than about mutexes.
  const runner_id_t RID_UNRELATED = 90;

  std::vector<transition_ptr> partners;
  partners.push_back(own(new mt::sem_init(20, THE_MUTEX)));
  partners.push_back(own(new mt::sem_init(21, ANOTHER_MUTEX)));
  partners.push_back(own(new mt::sem_post(22, THE_MUTEX)));
  partners.push_back(own(new mt::sem_post(23, ANOTHER_MUTEX)));
  partners.push_back(own(new mt::sem_wait(24, THE_MUTEX)));
  partners.push_back(own(new mt::sem_wait(25, ANOTHER_MUTEX)));
  partners.push_back(own(new mt::sem_destroy(26, THE_MUTEX)));
  partners.push_back(own(new mt::sem_destroy(27, ANOTHER_MUTEX)));
  partners.push_back(own(new mt::thread_start(RID_UNRELATED)));
  partners.push_back(own(new mt::thread_exit(RID_UNRELATED)));
  partners.push_back(own(new mt::process_exit(28)));
  partners.push_back(own(new mt::process_abort(29)));

  for (size_t i = 0; i < mutexes.size(); ++i) {
    for (size_t j = 0; j < partners.size(); ++j) {
      expect_both_orders(dr, *mutexes[i], *partners[j], false,
                         "mutex x non-mutex");
    }
  }
}

/// D-05's precedence must have survived the reparent: for the two pairs
/// `mutex_lock` declares by hand, the table's answer must be the one that
/// method returns.
///
/// The family agrees with both -- each reduces to the same `mutex_id` equality
/// -- so this cannot distinguish which one answered. That is the point: the
/// pairwise entries are kept *because* they are the authoritative statement
/// (D-20), and this assertion pins that they still compile, are still
/// registered, and have not drifted away from the family's answer.
void check_mutex_lock_pairwise_precedence() {
  const classic_dpor::dependency_relation_type dr =
      classic_dpor::default_dependencies();

  const mt::mutex_lock locks(1, THE_MUTEX);
  const mt::mutex_init inits(2, THE_MUTEX);
  const mt::mutex_lock locks_too(3, THE_MUTEX);
  const mt::mutex_init inits_other(4, ANOTHER_MUTEX);
  const mt::mutex_lock locks_other(5, ANOTHER_MUTEX);

  expect_both_orders(dr, locks, inits, locks.depends(&inits),
                     "mutex_lock x mutex_init must equal the pairwise answer");
  expect_both_orders(
      dr, locks, locks_too, locks.depends(&locks_too),
      "mutex_lock x mutex_lock must equal the pairwise answer");
  expect_both_orders(
      dr, locks, inits_other, locks.depends(&inits_other),
      "mutex_lock x mutex_init on two mutexes must equal the pairwise answer");
  expect_both_orders(
      dr, locks, locks_other, locks.depends(&locks_other),
      "mutex_lock x mutex_lock on two mutexes must equal the pairwise answer");
}

/// Neither the semaphore family nor the mutex family may declare a
/// whole-interface co-enabledness entry, because a blanket `true` would veto a
/// proof.
///
/// `call_or`'s two-sided rule asks both whole-interface entries when both types
/// declare one and returns the fallback if either answers it. `true` *is* the
/// co-enabledness fallback, so a family entry that can only answer `true`
/// silently overrides `thread_create::coenabled_with` and
/// `thread_join::coenabled_with`, whose `false` for a transition executed by
/// the created or joined thread is a proof: a thread cannot act before it is
/// created or after it has been joined.
///
/// This is the regression test for that defect. It is written on the values
/// rather than on the observer because the values genuinely differ: with a
/// family entry registered, every assertion below flips to `true`.
void check_family_coenabledness_does_not_veto_thread_proofs() {
  const classic_dpor::coenabled_relation_type cr =
      classic_dpor::default_coenabledness();

  const runner_id_t RID_TARGET = 50;
  const runner_id_t RID_UNRELATED = 51;
  const objid_t the_object = 1;

  const mt::thread_create creates(1, RID_TARGET);
  const mt::thread_join joins(2, RID_TARGET);
  const mt::thread_create creates_unrelated(3, RID_UNRELATED);
  const mt::thread_join joins_unrelated(4, RID_UNRELATED);

  // Every family leaf, executed by the thread being created or joined.
  std::vector<transition_ptr> by_target;
  by_target.push_back(own(new mt::sem_init(RID_TARGET, the_object)));
  by_target.push_back(own(new mt::sem_post(RID_TARGET, the_object)));
  by_target.push_back(own(new mt::sem_wait(RID_TARGET, the_object)));
  by_target.push_back(own(new mt::sem_destroy(RID_TARGET, the_object)));
  by_target.push_back(own(new mt::mutex_init(RID_TARGET, the_object)));
  by_target.push_back(own(new mt::mutex_lock(RID_TARGET, the_object)));
  by_target.push_back(own(new mt::mutex_unlock(RID_TARGET, the_object)));

  for (size_t i = 0; i < by_target.size(); ++i) {
    expect_both_orders(cr, creates, *by_target[i], false,
                       "a thread's creation is not co-enabled with that "
                       "thread's own operation");
    expect_both_orders(cr, joins, *by_target[i], false,
                       "a thread's join is not co-enabled with that thread's "
                       "own operation");

    // The control: the same claim must not collapse into "nothing is
    // co-enabled". An unrelated thread's creation or join says nothing.
    expect_both_orders(cr, creates_unrelated, *by_target[i], true,
                       "an unrelated thread's creation is co-enabled with a "
                       "family operation");
    expect_both_orders(cr, joins_unrelated, *by_target[i], true,
                       "an unrelated thread's join is co-enabled with a family "
                       "operation");
  }
}

}  // namespace

int main() {
  const std::vector<transition_ptr> shared_objects = make_roster(false);
  const std::vector<transition_ptr> distinct_objects = make_roster(true);

  check_distinct_executors(shared_objects);
  sweep_symmetry("shared object ids", shared_objects);
  sweep_symmetry("distinct object ids", distinct_objects);
  check_two_sided_collisions();
  check_unregistered_pair_alarm();
  check_process_transitions();
  check_cv_x_mutex();
  check_broadcast_and_destroy();
  check_semaphore_x_semaphore();
  check_semaphore_x_other_families();
  check_mutex_x_mutex();
  check_cv_x_mutex_pairwise_still_wins();
  check_mutex_x_other_families();
  check_mutex_lock_pairwise_precedence();
  check_family_coenabledness_does_not_veto_thread_proofs();

  if (g_failures > 0) {
    std::cerr << g_failures << " check(s) failed" << std::endl;
    return 1;
  }
  std::cout << "all relation checks passed" << std::endl;
  return 0;
}
