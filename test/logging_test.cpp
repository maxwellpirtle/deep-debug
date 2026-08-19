/// Unit tests for the lazy-logging machinery: the `log_severity` ternary
/// guard, `log_control::is_enabled`, and emitted-text identity through the
/// guarded path.
///
/// The guard is reached through the real `log_*` macros against a real
/// `logging::logger`; `is_enabled` agreement is checked against a locally
/// constructed twin of the installed filter, since `log_control` never
/// exposes its `active_filter`.
///
/// `log_control` is a process-wide singleton, so ordering matters twice:
/// the no-filter-installed case must run before any case installs a filter,
/// and every case that installs one restores `severity_filter(info)` (the
/// default `mcmini` installs at startup) so the remaining cases stay
/// order-independent.
///
/// Assertions are hand-rolled rather than `assert`: the Release build defines
/// `NDEBUG` and would compile every standard assertion away, leaving a test
/// that passes vacuously.

#include <iostream>
#include <sstream>
#include <string>

#include "mcmini/log/filter.hpp"
#include "mcmini/log/log_control.hpp"
#include "mcmini/log/logger.hpp"
#include "mcmini/log/severity_level.hpp"

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

using logging::severity_level;

severity_level severity_at(uint32_t value) {
  return static_cast<severity_level>(value);
}

void restore_default_filter() {
  logging::log_control::instance().allow_everything_over(severity_level::info);
}

/// The probe counts through a `std::ostream`-level free inserter: the stream
/// member template forwards every value to `ostream << value`, so this
/// inserter is reached exactly when the guard admitted the statement. A free
/// inserter on `logger::stream &` would lose overload resolution to the
/// member template and never count.
int g_probe_insertions = 0;

struct counting_probe {};

std::ostream &operator<<(std::ostream &os, const counting_probe &) {
  ++g_probe_insertions;
  return os << "probe";
}

/// MUST RUN FIRST: exercises the singleton before any filter is installed.
/// `log_raw` logs unconditionally when `active_filter` is null, so
/// `is_enabled` must answer true for every severity.
void check_null_filter_admits_everything() {
  logging::logger lg("logtest");
  for (uint32_t s = 0; s <= 9; ++s) {
    CHECK(lg.is_enabled(severity_at(s)),
          "no installed filter must admit severity " << s);
  }
  CHECK(logging::log_control::instance().is_enabled("", severity_level::debug),
        "no installed filter must admit an empty subsystem");
}

/// LOG-01: a filtered statement evaluates none of its arguments; an admitted
/// one evaluates each exactly once. Also the LOG-03 adjacency edge: a
/// statement at exactly the filter's minimum severity is admitted (`apply`
/// is a >= comparison).
void check_counting_probe() {
  logging::log_control::instance().set_filter(
      new logging::severity_filter(severity_level::info));
  logging::logger lg("logtest");

  std::stringstream captured;
  std::streambuf *previous = std::clog.rdbuf(captured.rdbuf());

  g_probe_insertions = 0;
  log_debug(lg) << "discarded " << counting_probe();
  CHECK(g_probe_insertions == 0,
        "a filtered statement must evaluate no argument, saw "
            << g_probe_insertions);
  CHECK(captured.str().empty(), "a filtered statement must emit nothing");

  log_info(lg) << "admitted " << counting_probe();
  CHECK(g_probe_insertions == 1,
        "an admitted statement must evaluate each argument exactly once, saw "
            << g_probe_insertions);
  CHECK(!captured.str().empty(),
        "a statement at exactly the minimum severity must emit");

  std::clog.rdbuf(previous);
  restore_default_filter();
}

/// LOG-03/D-08: `is_enabled` answers exactly as the installed filter's own
/// `apply` for a named subsystem, and maps an empty subsystem to the global
/// fallback exactly as `log_raw` does. The twin is a locally constructed
/// filter identical to the installed one. `expect_denials` guards the matrix
/// against vacuity for every filter that discriminates (the permissive
/// filter never denies, by design).
void check_agreement_with(const logging::filter &twin, const char *name,
                          bool expect_denials) {
  logging::log_control &lc = logging::log_control::instance();
  bool saw_admission = false;
  bool saw_denial = false;
  for (uint32_t s = 0; s <= 9; ++s) {
    const severity_level sev = severity_at(s);
    const bool named = twin.apply("logtest", sev);
    const bool fallback = twin.apply("global", sev);
    CHECK(lc.is_enabled("logtest", sev) == named,
          name << " disagrees with apply for `logtest` at severity " << s);
    CHECK(lc.is_enabled("", sev) == fallback,
          name << " disagrees with apply for the empty subsystem at severity "
               << s);
    saw_admission = saw_admission || named || fallback;
    saw_denial = saw_denial || !named || !fallback;
  }
  CHECK(saw_admission, name << " matrix never admitted anything");
  if (expect_denials) {
    CHECK(saw_denial, name << " matrix never denied anything");
  }
}

void check_agreement_matrix() {
  logging::log_control &lc = logging::log_control::instance();
  const logging::log_control::subsystem_list mapping = {
      {"logtest", severity_level::debug}, {"global", severity_level::error}};

  lc.set_filter(new logging::severity_filter(severity_level::info));
  check_agreement_with(logging::severity_filter(severity_level::info),
                       "severity_filter", true);

  lc.set_filter(new logging::whitelist_filter(mapping));
  check_agreement_with(logging::whitelist_filter(mapping), "whitelist_filter",
                       true);

  lc.set_filter(new logging::blacklist_filter(mapping));
  check_agreement_with(logging::blacklist_filter(mapping), "blacklist_filter",
                       true);

  lc.set_filter(new logging::permissive_filter());
  check_agreement_with(logging::permissive_filter(), "permissive_filter",
                       false);

  restore_default_filter();
}

/// LOG-03 empty-input edge: a default-constructed logger (subsystem == "")
/// answers `is_enabled` exactly as a whitelist keyed on the global fallback
/// name answers `apply("global", ...)` — the mapping `log_raw` applies.
void check_empty_subsystem_whitelist() {
  logging::log_control &lc = logging::log_control::instance();
  logging::logger unnamed;

  const logging::log_control::subsystem_list only_global = {
      {"global", severity_level::debug}};
  lc.set_filter(new logging::whitelist_filter(only_global));
  const logging::whitelist_filter twin(only_global);
  for (uint32_t s = 0; s <= 9; ++s) {
    const severity_level sev = severity_at(s);
    CHECK(unnamed.is_enabled(sev) == twin.apply("global", sev),
          "a default-constructed logger must answer as `global` at severity "
              << s);
  }
  restore_default_filter();
}

/// LOG-01/LOG-03 encoding edge: the content of a message admitted through
/// the guard path appears byte-for-byte in the emission. Captured by
/// swapping `std::clog`'s streambuf — `log_raw` and its prefix formatting
/// stay untouched, so the full prefix is deliberately not pinned.
void check_emitted_text_identity() {
  logging::log_control::instance().set_filter(
      new logging::severity_filter(severity_level::info));
  logging::logger lg("logtest");

  const std::string payload = "identity probe payload 42";
  std::stringstream captured;
  std::streambuf *previous = std::clog.rdbuf(captured.rdbuf());
  log_info(lg) << payload;
  std::clog.rdbuf(previous);

  CHECK(captured.str().find(payload) != std::string::npos,
        "admitted message content must appear byte-for-byte, captured: `"
            << captured.str() << "`");
  restore_default_filter();
}

/// LOG-01 empty-input edge: a statement with zero `<<` operands compiles on
/// both arms — `voidify::operator&` takes a const reference, so the prvalue
/// straight from `make_stream` binds. Its presence in this translation unit
/// is the compile-time half of the check; running both arms is the rest.
void check_zero_operand_statement() {
  logging::log_control::instance().set_filter(
      new logging::severity_filter(severity_level::info));
  logging::logger lg("logtest");

  std::stringstream captured;
  std::streambuf *previous = std::clog.rdbuf(captured.rdbuf());
  log_debug(lg);
  log_info(lg);
  std::clog.rdbuf(previous);

  CHECK(captured.str().empty(),
        "a zero-operand statement must emit nothing on either arm");
  restore_default_filter();
}

} // namespace

int main() {
  check_null_filter_admits_everything();
  check_counting_probe();
  check_agreement_matrix();
  check_empty_subsystem_whitelist();
  check_emitted_text_identity();
  check_zero_operand_statement();

  if (g_failures > 0) {
    std::cerr << g_failures << " check(s) failed" << std::endl;
    return 1;
  }
  std::cout << "all logging checks passed" << std::endl;
  return 0;
}
