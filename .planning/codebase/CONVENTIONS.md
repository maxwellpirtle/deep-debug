# Coding Conventions

**Analysis Date:** 2026-08-08

## Naming Patterns

**Files:**
- C++ implementation: `.cpp` extension
- C++ headers: `.hpp` extension
- C implementation: `.c` extension
- C headers: `.h` extension
- Template implementations: `.c` suffix (e.g., `template/loop.c`)
- Examples follow the naming of what they demonstrate (e.g., `producer-consumer.c`)

**Functions:**
- All lowercase with underscores: `translate_recorded_object_to_model()`, `filename_from_path()`, `signal_tracker_sig_handler()`
- Static/helper functions prefixed with context: `handle_incoming_signals()`, `is_likely_debugging()`
- Accessor methods use get/set prefixes: `get_enabled_runners()`, `set_filter()`, `set_signal()`

**Variables:**
- All lowercase with underscores: `tid_self`, `global_var_thread1`, `current_sem`, `pending_transitions`
- Static/module-level variables prefixed with context: `active_filter`, `mutex_resource`
- Thread-local variables marked with `MCMINI_THREAD_LOCAL` or `thread_local`
- Loop counters: `i`, `cur`, `lineno` (contextual, short names acceptable for scope)

**Types and Classes:**
- Classes use snake_case: `class program`, `class logger`, `class signal_tracker`, `class asserts`, `class log_control`
- Structs for data holders: `struct forks`, `struct pthread_map`, `struct sigaction`
- Type aliases end with `_t`: `runner_id_t`, `trid_t`, `thread_routine`, `free_function`
- Nested types follow parent naming: `objects::mutex::state`, `logging::severity_level`
- Exceptions as inner classes: `signal_tracker::interrupted_error`

**Constants and Macros:**
- All uppercase with underscores: `MAX_TOTAL_TRANSITIONS_IN_PROGRAM`, `THREAD_SHM_OFFSET`, `RID_MAIN_THREAD`, `RUNNER_ID_MAX`
- Prefixed with context when appropriate: `MCMINI_INLINE`, `MCMINI_EXPORT`, `MCMINI_PRIVATE`
- Feature test macros: `_GNU_SOURCE`, `_XOPEN_SOURCE_EXTENDED`
- Predicate macros return boolean: `FORK_IS_CHILD_PID(pid)`, `pthread_equal(cur->thread, t)`

**Namespaces:**
- Used to organize logical domains: `namespace logging`, `namespace model`, `namespace objects`, `namespace extensions`, `namespace model_checking`, `namespace real_world`
- Single-level namespaces per logical area
- Functions use fully qualified names or `using namespace` declarations at file scope

## Code Style

**Formatting:**
- Tool: `clang-format` (see `.clang-format`)
- Indent width: 2 spaces
- Column limit: 80 characters
- No tabs (`UseTab: Never`)
- Trailing commas: None allowed (`InsertTrailingCommas: None`)
- Braces on same line for all structures (`BreakBeforeBraces: Attach`)
- Access modifiers indented at class level (`AccessModifierOffset: -1`)

**Brace Wrapping:**
- Classes, structs, enums, unions: braces on same line as declaration
- Functions: braces on same line
- Namespaces: braces on same line
- Cases and labels: braces on same line, labels NOT wrapped in braces
- `if`/`else`/`while`: braces on same line, but `else` on same line as closing brace

**Alignment:**
- Consecutive assignments: NOT aligned
- Operators: aligned (`AlignOperands: Align`)
- Trailing comments: aligned to column 80 minimum (`AlignTrailingComments: true`)
- Escaped newlines: aligned left (`AlignEscapedNewlines: Left`)
- After open bracket: aligned (`AlignAfterOpenBracket: Align`)

**Function Design:**
- Single-line functions allowed: `static size_t digits(uint32_t x) { ... }`
- Single-line lambdas allowed
- Short blocks allowed on one line if simple
- Parameters break to next line if needed, with continuation indent of 4 spaces
- Function names NOT indented when wrapped (`IndentWrappedFunctionNames: false`)

**Template Declarations:**
- Always break after template keyword
- Always break template declarations across lines (`AlwaysBreakTemplateDeclarations: Yes`)

## Linting

**Framework:** `clang-tidy`
- Config: `.clang-tidy` at root
- Enabled checks: `clang-diagnostic-*`, `clang-analyzer-*`
- System headers NOT analyzed (`SystemHeaders: false`)
- Format style: none (handled by clang-format)
- Function size threshold: 800 statements

**Check Options:**
- Namespace comment threshold: 10 lines
- Ignore public-only member variables in classes
- Braces around single statements: enforced for short statement lines (1+)

## Import Organization

**Order (by priority):**
1. System headers in angle brackets: `<ext/.*\.h>` (priority 2)
2. Standard C/C++ headers: `<.*\.h>`, `<.*>` (priority 1-2)
3. Project headers: relative paths with quotes (priority 3)

**Style:**
- Includes grouped by category (`IncludeBlocks: Regroup`)
- Case-sensitive sorting: `SortIncludes: CaseSensitive`
- Main source regex: `([-_](test|unittest))?$` to identify test files
- Comments: `IWYU pragma` supported (`CommentPragmas: '^ IWYU pragma:'`)

**Example from code:**
```cpp
#include "mcmini/log/logger.hpp"
#include <cmath>
#include <vector>
#include "mcmini/log/log_control.hpp"
#include "mcmini/log/severity_level.hpp"
```

## Error Handling

**Patterns in C++:**
- Exceptions for assertion violations: `std::invalid_argument`, `std::logic_error`
- Custom exceptions inherit from `std::exception`: `signal_tracker::interrupted_error`
- Exception methods implement `what() const noexcept override`
- Prefer throwing over returning error codes in higher-level code

**Patterns in C:**
- Return codes for success/failure: `PTHREAD_SUCCESS (0)`, error on non-zero
- `perror()` for system error reporting
- `assert()` for programmer errors (debug-only)
- Exit codes: `EXIT_FAILURE` for abnormal termination

**Custom Assertion System (C++):**
- `asserts::assert_condition(bool cond, string why)`: enforced preconditions, throws `std::invalid_argument`
- `asserts::assert_invariant(bool cond, string why)`: program invariants, throws `std::logic_error`
- Both support overloads for `const char*` and `std::string` parameters
- Located: `include/mcmini/misc/asserts.hpp`

**Signal Handling:**
- Signals trigger exceptions: `throw interrupted_error(sig)`
- Consumed signals: `try_consume_signal(int sig)` - atomic check-and-decrement
- Bad signals (SIGSEGV, SIGABRT, etc.) trigger `std::terminate()` directly

## Logging

**Framework:** Custom logging system in `src/mcmini/log/`

**API:**
- Create logger: `logging::logger logger_name("subsystem_name")`
- Log with severity macros: `log_debug(logger)`, `log_error(logger)`, `log_critical(logger)`
- Stream-based: `log_debug(logger) << "message" << value`

**Severity Levels:**
- `NOTHING`, `VERY_VERBOSE`, `VERBOSE`, `DEBUG`, `INFO`, `UNEXPECTED`, `ERROR`, `CRITICAL`, `ABORT`, `EVERYTHING`

**Filtering:**
- Permissive filter: `allow_everything()`
- Severity-based filter: `allow_everything_over(severity_level level)`
- Blacklist filter: `blacklist(blacklist_filter bl)`

**Output Format:**
- Format: `[PID] subsystem (instance) HH:MM:SS SEVERITY file:line: message`
- Subsystem padded to 5 characters
- File:line padded to 20 characters
- Multi-line messages prefixed with line number

**Located:** `include/mcmini/log/logger.hpp`

## Comments

**DocComments (JavaDoc style):**
```cpp
/**
 * @brief One-line summary of what this does.
 *
 * @param param1 description of first parameter
 * @param param2 description of second parameter
 * @return what this returns
 * @throws std::invalid_argument if condition X
 */
```

**When to Comment:**
- Document public API in headers with full doc comments
- Add explanatory comments for non-obvious implementation decisions
- Preconditions and postconditions in docstrings
- Invariants in struct/class docstrings
- TODO comments for incomplete work: `// TODO: description`
- FIXME comments for bugs: not observed in codebase

**What NOT to Comment:**
- Self-documenting code (avoid "setting x to 5")
- Comments that restate the code (not in this codebase)

**Inline Comments:**
- Keep to minimum; prefer clear variable/function names
- Note historical context or design rationale: `// NOTE: insert_pthread_map() prepends...`
- Explain non-obvious algorithms: `// From cppreference on restrict pointers...`
- Reference external specifications: `// See https://...`

## Module Design

**Exports:**
- Public API in `.hpp` header files
- Implementation in `.cpp` implementation files
- Inline implementations allowed for small functions
- Static functions/variables for internal use only

**Header Include Guards:**
- `#pragma once` preferred over `#ifndef`
- Located at very top of header file

**Public vs Private:**
- Use `public:`, `private:` access modifiers
- Member variables typically private
- Getters/setters for data access
- Static helper functions marked static

**Singleton Pattern:**
- Used for global state: `signal_tracker::instance()`
- Implemented with static function returning reference to static local
- Thread-safe by C++11 static initialization guarantees

## Data Structures

**Volatile Pointers:**
- Used for interprocess communication: `volatile struct mcmini_shm_file *`
- Volatile semantics prevent compiler optimizations

**Type-Safe Integer IDs:**
- `runner_id_t` for thread runners: `uint16_t`
- `trid_t` for transition IDs: `uint64_t`
- `objid_t` for object IDs (inferred from code patterns)

**Callbacks:**
- Function pointers for callbacks: `typedef void (*free_function)(void *);`
- Function types: `typedef void *(*thread_routine)(void *);`
- Used in contexts requiring runtime dispatch

---

*Convention analysis: 2026-08-08*
