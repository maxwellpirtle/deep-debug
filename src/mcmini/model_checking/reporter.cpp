#include "mcmini/model_checking/reporter.hpp"
#include "mcmini/signal.hpp"

using namespace model;
using namespace model_checking;

void reporter::trace_completed(const algorithm::context &c,
                               const stats &stats) const {
  if (!verbose)
    return;
  std::stringstream ss;
  ss << "TRACE " << stats.trace_id << "\n";
  for (const auto &t : c.get_model().get_trace()) {
    ss << "thread " << t->get_executor() << ": " << t->to_string() << "\n";
  }
  ss << "\nNEXT THREAD OPERATIONS\n";
  for (const auto &tpair : c.get_model().get_pending_transitions()) {
    ss << "thread " << tpair.first << ": " << tpair.second->to_string() << "\n";
  }
  std::cout << ss.str();
  std::cout.flush();
}

void reporter::deadlock(const algorithm::context &c, const stats &stats) const {
  std::cerr << "DEADLOCK" << std::endl;
  std::stringstream ss;
  for (const auto &t : c.get_model().get_trace()) {
    ss << "thread " << t->get_executor() << ": " << t->to_string() << "\n";
  }
  ss << "\nNEXT THREAD OPERATIONS\n";
  for (const auto &tpair : c.get_model().get_pending_transitions()) {
    ss << "thread " << tpair.first << ": " << tpair.second->to_string() << "\n";
  }
  std::cout << ss.str();
  std::cout.flush();
}

void reporter::undefined_behavior(
    const algorithm::context &c, const stats &stats,
    const undefined_behavior_exception &ub) const {
  std::cerr << "UNDEFINED BEHAVIOR:\n" << ub.what() << std::endl;
  std::stringstream ss;
  ss << "TRACE " << stats.trace_id << "\n";
  for (const auto &t : c.get_model().get_trace()) {
    ss << "thread " << t->get_executor() << ": " << t->to_string() << "\n";
  }
  ss << "\nNEXT THREAD OPERATIONS\n";
  for (const auto &tpair : c.get_model().get_pending_transitions()) {
    ss << "thread " << tpair.first << ": " << tpair.second->to_string() << "\n";
  }
  std::cout << ss.str();
  std::cout.flush();
}

void reporter::abnormal_termination(
    const algorithm::context &c, const stats &stats,
    const real_world::process::termination_error &ub) const {
  std::cerr << "Abnormally Termination (signo: " << ub.signo
            << ", signal: " << sig_to_str.at(ub.signo) << "):\n"
            << ub.what() << std::endl;

  std::stringstream ss;
  ss << "TRACE " << stats.trace_id << "\n";
  for (const auto &t : c.get_model().get_trace()) {
    ss << "thread " << t->get_executor() << ": " << t->to_string() << "\n";
  }
  const transition *terminator =
      c.get_model().get_pending_transition_for(ub.culprit);
  ss << "thread " << terminator->get_executor() << ": "
     << terminator->to_string() << "\n";

  ss << "\nNEXT THREAD OPERATIONS\n";
  for (const auto &tpair : c.get_model().get_pending_transitions()) {
    if (tpair.first == terminator->get_executor()) {
      ss << "thread " << tpair.first << ": executing"
         << "\n";
    } else {
      ss << "thread " << tpair.first << ": " << tpair.second->to_string()
         << "\n";
    }
  }
  ss << stats.total_transitions + 1 << " total transitions executed"
     << "\n";
  std::cout << ss.str();
  std::cout.flush();
}