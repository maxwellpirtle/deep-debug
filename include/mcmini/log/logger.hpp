#pragma once

#include <iostream>
#include <iterator>
#include <mutex>
#include <sstream>
#include <string>
#include <unordered_set>

#include "mcmini/log/log_control.hpp"
#include "mcmini/log/severity_level.hpp"
#include "mcmini/model/program.hpp"

// The ternary evaluates exactly one arm, so a filtered statement evaluates
// none of its `<<` arguments, constructs no stream, and allocates nothing.
// `logging::voidify::operator&` binds looser than `<<` and tighter than `?:`,
// so it swallows the whole chained expression and yields `void` to match the
// discard arm.
#define log_severity(logger, severity)                                         \
  !(logger).is_enabled(severity)                                               \
      ? (void)0                                                                \
      : logging::voidify() &                                                   \
            (logger).make_stream(__FILE__, __LINE__, severity)
#define log_very_verbose(logger)                                               \
  log_severity(logger, logging::severity_level::very_verbose)
#define log_verbose(logger)                                                    \
  log_severity(logger, logging::severity_level::verbose)
#define log_debug(logger) log_severity(logger, logging::severity_level::debug)
#define log_info(logger) log_severity(logger, logging::severity_level::info)
#define log_unexpected(logger)                                                 \
  log_severity(logger, logging::severity_level::unexpected)
#define log_error(logger) log_severity(logger, logging::severity_level::error)
#define log_critical(logger)                                                   \
  log_severity(logger, logging::severity_level::critical)
#define log_abort(logger) log_severity(logger, logging::severity_level::abort)

namespace logging {
class logger {
public:
  logger() = default;
  logger(const std::string &subsystem) : subsystem(subsystem) {}

public:
  template <typename T> void set_instance(T *instance) {
    std::stringstream strm;
    strm << "0x" << std::hex << reinterpret_cast<uint64_t>(instance);
    this->instance = strm.str();
  }

public:
  struct stream {
  public:
    ~stream() { flush(); }
    template <typename T> stream &operator<<(const T &value) {
      ostream << value;
      return *this;
    }

    template <typename T> stream &operator<<(const std::unordered_set<T> &set) {
      ostream << "[";
      for (const T &t : set)
        ostream << t << ", ";
      ostream << "]";
      return *this;
    }

    stream &operator<<(const model::program &prog) {
      prog.dump_state(this->ostream);
      return *this;
    }

    // One severity per statement, named by the `log_*` macro. Deleted rather
    // than removed: `severity_level` is an unscoped `uint32_t` enum, so
    // without this overload a stray severity insertion would resolve to the
    // generic member template above and silently print an integer.
    stream &operator<<(severity_level) = delete;

  private:
    stream &operator=(stream &&) = default;
    stream(stream &&) = default;
    explicit stream(logger *log, const char *file, int line,
                    severity_level severity)
        : log(log), file(file), line(line), current_severity(severity) {}
    void flush() {
      if (ostream.str() != "") {
        this->log->log_raw(ostream.str(), current_severity, file, line);
        this->ostream = std::stringstream();
      };
    }

  private:
    logger *log;
    const char *file;
    int line;

    severity_level current_severity;
    std::stringstream ostream;

  private:
    friend class logger;
  };

public:
  stream make_stream(const char *file, int line, severity_level severity) {
    return logging::logger::stream(this, file, line, severity);
  }

public:
  inline bool is_enabled(severity_level severity) {
    return log_control::instance().is_enabled(subsystem, severity);
  }

  inline void log_raw(const std::string &message, severity_level severity,
                      const char *file = __FILE__, int line = __LINE__) {
    log_control::instance().log_raw(instance, subsystem, message, severity,
                                    file, line);
  }

private:
  std::string instance;
  std::string subsystem;

private:
  friend struct stream;
};

// Swallows the stream expression in `log_severity`'s enabled arm and yields
// `void` so both ternary arms agree. Takes a const reference so a statement
// with zero `<<` operands (a prvalue straight from `make_stream`) still binds.
struct voidify {
  void operator&(const logger::stream &) {}
};
} // namespace logging
