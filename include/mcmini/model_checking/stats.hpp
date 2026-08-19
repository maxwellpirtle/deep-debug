#pragma once

#include <cstdint>

namespace model_checking {
struct stats {
  uint32_t trace_id = 1;
  uint32_t total_transitions = 0;

  /**
   * Whether the search unwound the DPOR stack without ever hitting the
   * per-trace transition limit.
   *
   * A truncated search is otherwise indistinguishable from a speedup: fewer
   * traces, less time.
   */
  bool exhausted = false;

  /** The wall-clock duration of model checking alone, in whole milliseconds. */
  uint64_t check_ms = 0;

  uint32_t deadlocks = 0;
  uint32_t undefined_behaviors = 0;
  uint32_t abnormal_terminations = 0;
  uint32_t nonzero_exit_codes = 0;
};
}  // namespace model_checking
