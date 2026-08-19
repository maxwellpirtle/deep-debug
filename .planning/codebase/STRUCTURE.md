# Codebase Structure

**Analysis Date:** 2026-08-08

## Directory Layout

```
/home/parallels/deep-debug/
├── include/mcmini/              # Public header files, organized by layer
│   ├── lib/                     # Library injection interfaces (C headers)
│   │   ├── entry.h              # Initialization (prevent ASLR, install handlers)
│   │   ├── log.h                # Logging from injected library
│   │   ├── sig.h                # Signal handling for pause points
│   │   ├── template.h           # Template-based execution boilerplate
│   │   └── interception.h       # Function wrapping interface
│   ├── model/                   # Model abstractions (C++ headers)
│   │   ├── program.hpp          # Program = trace + state sequence + pending transitions
│   │   ├── state.hpp            # Abstract state interface
│   │   ├── transition.hpp       # Transition (state transformation) abstraction
│   │   ├── visible_object.hpp   # Container for object history
│   │   ├── visible_object_state.hpp # Base for state snapshots
│   │   ├── runner_state.hpp     # Base class for runner states (threads)
│   │   ├── exception.hpp        # Exceptions (undefined behavior, etc)
│   │   ├── config.hpp           # Model configuration (depth, deadlock detection)
│   │   ├── objects/             # Concrete visible object types
│   │   │   ├── thread.hpp       # Thread state machine (embryo/running/exited/killed)
│   │   │   ├── mutex.hpp        # Mutex state machine (uninitialized/unlocked/locked/destroyed)
│   │   │   ├── semaphore.hpp    # Semaphore state (count, waiters)
│   │   │   └── condition_variables.hpp # Condition variable state (waiters, signaled)
│   │   ├── transitions/         # Concrete transition types (operations)
│   │   │   ├── thread/          # Thread operations (create, start, exit, join)
│   │   │   ├── mutex/           # Mutex operations (init, lock, unlock)
│   │   │   ├── semaphore/       # Semaphore operations (init, wait, post, destroy)
│   │   │   ├── condition_variables/ # Condition variable operations (wait, signal, broadcast)
│   │   │   └── process/         # Process operations (exit, abort)
│   │   ├── state/               # State implementations
│   │   │   ├── diff_state.hpp   # State that stores only diffs from previous
│   │   │   ├── detached_state.hpp # State for detached objects
│   │   │   ├── state_sequence.hpp # Sequence of immutable states
│   │   │   └── transition_sequence.hpp # Sequence of executed transitions
│   │   ├── transition_registry.hpp # Maps runtime type IDs to transition callbacks
│   │   └── pending_transitions.hpp # Maps runner IDs to next operations
│   ├── model_checking/          # Verification algorithms
│   │   ├── algorithm.hpp        # Abstract algorithm interface
│   │   ├── algorithms/          # Concrete algorithm implementations
│   │   │   ├── classic_dpor.hpp # DPOR algorithm (Flanagan-Godefroid 2005)
│   │   │   └── classic_dpor/    # DPOR internals
│   │   │       ├── clock_vector.hpp # Causality tracking
│   │   │       ├── runner_item.hpp  # Per-runner state in DPOR stack
│   │   │       └── stack_item.hpp   # DPOR stack frame (state + transition + backtrack set)
│   │   ├── reporter.hpp         # Formats and reports violations
│   │   └── stats.hpp            # Statistics collection
│   ├── real_world/              # Real process management
│   │   ├── process.hpp          # Abstract process proxy interface
│   │   ├── process_source.hpp   # Factory for spawning processes
│   │   ├── target.hpp           # Target program descriptor
│   │   ├── process/             # Process implementations
│   │   │   ├── local_linux_process.hpp # Concrete Linux process (fork-based)
│   │   │   ├── fork_process_source.hpp # Spawns processes via fork()
│   │   │   ├── multithreaded_fork_process_source.hpp # fork() for multi-threaded targets
│   │   │   ├── dmtcp_process_source.hpp # Spawns from DMTCP checkpoints
│   │   │   ├── dmtcp_coordinator.hpp # DMTCP protocol client
│   │   │   ├── resources.hpp    # Process resource management (memory, FDs)
│   │   │   ├── wait.h           # Wait-on-process helpers
│   │   │   └── template_process.h # Template-based process execution
│   │   ├── mailbox/             # IPC mechanism
│   │   │   └── runner_mailbox.h # Mailbox struct passed between process and coordinator
│   │   ├── shm.hpp              # Shared memory access primitives
│   │   ├── fifo.hpp             # FIFO communication channel
│   │   ├── dmtcp_target.hpp     # DMTCP target descriptor
│   │   └── remote_address.hpp   # Address mapping between process and model
│   ├── coordinator/             # Synchronization layer
│   │   ├── coordinator.hpp      # Main coordinator (Model ↔ Process sync)
│   │   ├── model_to_system_map.hpp # Maps model object IDs to process memory
│   │   └── restore-objects.hpp  # Object restoration after checkpoint
│   ├── log/                     # Logging system
│   │   ├── logger.hpp           # Logger implementation
│   │   ├── filter.hpp           # Log filtering by module/level
│   │   ├── log_control.hpp      # Global log control settings
│   │   └── severity_level.hpp   # Log severity enum and parser
│   ├── misc/                    # Utilities and helpers
│   │   ├── append-only.hpp      # Append-only container
│   │   ├── asserts.hpp          # Custom assertions
│   │   ├── ini-parser.hpp       # INI file parsing
│   │   ├── injective_function.hpp # Injective function table (for transitions)
│   │   ├── ddt.hpp              # Double dispatch table (DDT for dependency relations)
│   │   ├── cond/                # Condition variable wake policies
│   │   │   ├── cond_var_policy.hpp # Base policy interface
│   │   │   ├── cond_var_default_policy.hpp # Standard waking behavior
│   │   │   ├── cond_var_arbitrary_policy.hpp # Allow any thread wake
│   │   │   ├── cond_var_single_grp_policy.hpp # Only wake one group
│   │   │   └── cond_var_wakegroup.hpp # Thread grouping for waking
│   │   └── extensions/          # C++ helpers
│   │       ├── memory.hpp       # Memory utilities
│   │       └── unique_ptr.hpp   # Custom unique_ptr overloads
│   ├── spy/                     # Spy/instrumentation headers
│   │   ├── intercept/           # Interception point definitions
│   │   │   ├── interception.h   # Interception hook declarations
│   │   │   └── wrappers.h       # Wrapper function declarations
│   │   └── checkpointing/       # Checkpoint data structures
│   │       ├── alloc.h          # Memory allocation tracking
│   │       ├── objects.h        # Object state snapshots
│   │       ├── transitions.h    # Transition recording
│   │       ├── record.h         # Record of executed operations
│   │       ├── rec_list.h       # List of records
│   │       └── cv_status.h      # Condition variable status enums
│   ├── common/                  # Shared structures (used by lib and coordinator)
│   │   ├── thread.h             # Thread ID definition
│   │   ├── exit.h               # Exit handling
│   │   ├── shm_config.h         # Shared memory configuration
│   │   └── dmtcp.h              # DMTCP integration
│   ├── plugins/                 # Plugin system
│   │   ├── loader.hpp           # Plugin loader
│   │   └── mcmini.h             # Plugin interface (C)
│   ├── mcmini.h                 # C public API
│   ├── mcmini.hpp               # C++ public API
│   ├── plugins.h                # Plugin declarations
│   ├── mem.h                    # Memory allocation wrapper
│   ├── signal.hpp               # Signal handling primitives
│   ├── defines.h                # Platform-specific defines
│   ├── constants.hpp            # Global constants
│   ├── forwards.hpp             # Forward declarations
│   └── Thread_queue.h           # Thread queue data structure
│
├── src/
│   ├── lib/                     # Injected library (linked into target process)
│   │   ├── main.c               # Shared memory initialization (called at startup)
│   │   ├── entry.c              # Process entry point setup
│   │   ├── interception.c       # Function interception hooks (wrappers)
│   │   ├── wrappers.c           # POSIX function wrappers (mutex, thread, semaphore)
│   │   ├── record.c             # Transition recording and serialization
│   │   ├── log.c                # Logging from injected library
│   │   ├── sem-wrappers.c       # Semaphore-specific wrappers
│   │   ├── dmtcp-callback.c     # DMTCP integration callbacks
│   │   ├── template/            # Template-based execution
│   │   │   ├── loop.c           # Event loop template for pausing/resuming
│   │   │   └── sig.c            # Signal handling for pause points
│   │   └── CMakeLists.txt       # Build configuration for injected library
│   │
│   ├── mcmini/                  # Verification engine (coordinator + model checker)
│   │   ├── mcmini.cpp           # Main coordinator orchestration
│   │   ├── model/               # Model implementations
│   │   │   ├── program.cpp      # Program state management
│   │   │   ├── state_sequence.cpp # State history management
│   │   │   ├── transition_registry.cpp # Runtime transition mapping
│   │   │   ├── detached_state.cpp # Detached object state
│   │   │   ├── diff_state.cpp   # Differential state storage
│   │   │   ├── visible_object.cpp # Visible object history
│   │   │   ├── transitions/     # Transition implementations
│   │   │   │   ├── thread.cpp   # Thread transition logic
│   │   │   │   ├── mutex.cpp    # Mutex transition logic
│   │   │   │   ├── semaphore.cpp # Semaphore transition logic
│   │   │   │   ├── condition_variables.cpp # Cond var transition logic
│   │   │   │   └── process.cpp  # Process exit transition logic
│   │   │   └── cond_var_*.cpp   # Condition variable policy implementations
│   │   │
│   │   ├── model_checking/      # Algorithm implementations
│   │   │   ├── algorithms/
│   │   │   │   ├── classic_dpor.cpp # DPOR algorithm main loop
│   │   │   │   └── clock_vector.cpp # Clock vector operations
│   │   │   ├── reporter.cpp     # Violation reporting
│   │   │   └── stats.cpp        # Statistics tracking
│   │   │
│   │   ├── real_world/          # Process management implementations
│   │   │   ├── process/
│   │   │   │   ├── local_linux_process.cpp # Fork-based process execution
│   │   │   │   ├── fork_process_source.cpp # fork() spawner
│   │   │   │   ├── dmtcp_process_source.cpp # DMTCP spawner
│   │   │   │   ├── dmtcp_coordinator.cpp # DMTCP protocol handling
│   │   │   │   ├── resources.cpp # Process resource tracking
│   │   │   │   └── multithreaded_fork.c # Multi-threaded fork handling
│   │   │   ├── target.cpp       # Target descriptor operations
│   │   │   ├── fifo.cpp         # FIFO communication
│   │   │   ├── shm.cpp          # Shared memory management
│   │   │   ├── Thread_queue.c   # Thread queue operations
│   │   │   └── mailbox handling
│   │   │
│   │   ├── coordinator/         # Synchronization implementation
│   │   │   ├── coordinator.cpp  # Main coordination logic (execute_runner, discover)
│   │   │   └── restore-objects.cpp # Checkpoint object restoration
│   │   │
│   │   ├── log/                 # Logging implementation
│   │   │   ├── logger.cpp       # Logger implementation
│   │   │   └── filter.cpp       # Log filtering
│   │   │
│   │   ├── signal.cpp           # Signal handling
│   │   └── constants.cpp        # Global constants definitions
│   │
│   ├── common/                  # Shared C code (used by both lib and coordinator)
│   │   ├── exit.c               # Exit handling implementation
│   │   ├── mem.c                # Memory allocation wrappers
│   │   ├── shm_config.c         # Shared memory config setup
│   │   ├── runner_mailbox.c     # Mailbox IPC implementation
│   │   ├── multithreaded_fork.c # Fork for multi-threaded processes
│   │   └── CMakeLists.txt
│   │
│   ├── examples/                # Example test programs
│   │   ├── hello-world.c        # Simple hello world (no concurrency)
│   │   ├── deadly-embrace.c     # Deadlock example (two mutexes)
│   │   ├── producer-consumer.c  # Producer-consumer with semaphores
│   │   ├── recycled-thread.c    # Thread creation/destruction
│   │   ├── cv-hello-world.c     # Condition variable example
│   │   ├── cv-test.c            # Complex condition variable test
│   │   ├── fifo.cpp             # FIFO communication
│   │   ├── test.cpp             # Generic test harness
│   │   └── CMakeLists.txt
│   │
│   └── CMakeLists.txt           # Main build configuration
│
├── test/                        # Test suite
│   ├── assertions/              # Assertion-based tests (for McMini features)
│   ├── segfaults/               # Segmentation fault detection tests
│   └── CMakeLists.txt
│
├── include/dmtcp/               # DMTCP integration headers
│   ├── version.h                # DMTCP version info
│   └── dmtcp.h                  # DMTCP C API
│
├── .planning/                   # GSD planning documents
│   └── codebase/                # Codebase analysis (this document)
│
├── docs/                        # Project documentation
├── script/                      # Utility scripts
├── sketch/                      # Design sketches and notes
├── build/                       # CMake build artifacts (ignored in analysis)
├── out/                         # Alternative build outputs (ignored in analysis)
│
├── CMakeLists.txt               # Root CMake build file
├── CMakePresets.json            # CMake configuration presets
├── README.md                    # Project overview
├── mcmini-architecture.md       # Architecture design document
└── Cond_Var_Readme.md           # Condition variable documentation
```

## Directory Purposes

**include/mcmini/lib/:**
- Purpose: Public API for injected library; headers used by target process at compile time
- Contains: Initialization, logging, signal handling, interception point declarations
- Key files: `entry.h` (setup), `interception.h` (hook declarations)

**include/mcmini/model/:**
- Purpose: Core model abstractions (program, state, transition, visible objects)
- Contains: Interfaces and concrete implementations of model components
- Key files: `program.hpp` (trace container), `state.hpp` (state interface), `transition.hpp` (operation interface)

**include/mcmini/model_checking/:**
- Purpose: Verification algorithm interfaces and implementations
- Contains: Abstract algorithm interface, DPOR implementation, reporter, statistics
- Key files: `algorithm.hpp` (interface), `classic_dpor.hpp` (implementation)

**include/mcmini/real_world/:**
- Purpose: Bridge between model and actual processes
- Contains: Process proxy, process factory, checkpoint management, IPC
- Key files: `process.hpp` (process interface), `process_source.hpp` (factory), process implementations

**include/mcmini/coordinator/:**
- Purpose: Synchronization logic for model ↔ process correspondence
- Contains: Main coordinator, model-to-system address mapping
- Key files: `coordinator.hpp` (sync orchestration)

**include/mcmini/misc/:**
- Purpose: Utility code and helper abstractions
- Contains: Condition variable policies, double dispatch tables, append-only containers
- Special: `cond/` has pluggable wake policies for condition variables

**src/lib/:**
- Purpose: Injected into target process; intercepts and records operations
- Contains: C code for interception, shared memory setup, transition recording
- Key files: `main.c` (SHM init), `interception.c` (hooks), `record.c` (serialization)

**src/mcmini/:**
- Purpose: Verification engine (coordination + model checking)
- Contains: C++ implementations of model layer, algorithm, coordinator, real world
- Key files: `mcmini.cpp` (orchestrator), `coordinator/coordinator.cpp` (sync loop)

**src/common/:**
- Purpose: Shared utilities used by both injected library and coordinator
- Contains: Memory management, exit handling, mailbox IPC, shared memory config
- Key files: `runner_mailbox.c` (IPC struct), `shm_config.c` (SHM setup)

**src/examples/:**
- Purpose: Example programs to verify; used as test cases
- Contains: Small concurrent programs demonstrating features (deadlock, producer-consumer, etc)
- Key files: `deadly-embrace.c` (deadlock), `producer-consumer.c` (semaphores)

**test/:**
- Purpose: Test suite for McMini itself
- Contains: Assertion-based tests, segmentation fault detection tests

## Key File Locations

**Entry Points:**
- `src/mcmini/mcmini.cpp`: Coordinator orchestration and DPOR setup
- `src/lib/main.c`: Process-side shared memory initialization
- `src/lib/entry.c`: Process startup setup

**Configuration:**
- `include/mcmini/model/config.hpp`: Model configuration (max depth, stop_at_first_deadlock, etc)
- `CMakeLists.txt`: Build system

**Core Logic:**
- `include/mcmini/model/program.hpp`: Program abstraction (trace + state + pending transitions)
- `include/mcmini/coordinator/coordinator.hpp`: Synchronization logic
- `src/mcmini/model_checking/algorithms/classic_dpor.cpp`: DPOR algorithm implementation

**Testing:**
- `src/examples/`: Small example programs that demonstrate features
- `test/assertions/`: Test cases verifying McMini functionality
- `test/segfaults/`: Segmentation fault detection tests

## Naming Conventions

**Files:**
- Headers: `.hpp` (C++), `.h` (C)
- Source: `.cpp` (C++), `.c` (C)
- Pattern: Filename matches primary class name (e.g., `program.hpp` contains `class program`)

**Directories:**
- Pattern: Lowercase, separates by layer (model, real_world, coordinator, etc)
- Abbreviations: `log` (logging), `misc` (miscellaneous), `spy` (instrumentation)

**Classes:**
- Namespaced: `model::`, `real_world::`, `model_checking::`, `logging::`
- Pattern: `snake_case` for namespaces, `snake_case` for class names (e.g., `model::visible_object`)
- Subclasses: Nested under layer namespace (e.g., `model::objects::mutex`)

**Enums:**
- State enums: Inside concrete classes (e.g., `mutex::state`)
- Values: SCREAMING_SNAKE_CASE (e.g., `state::locked`, `MUTEX` type)

**Functions/Methods:**
- Pattern: `snake_case`
- Access: `get_X()` for getters, `set_X()` for setters, `is_X()` for predicates

## Where to Add New Code

**New Synchronization Object (e.g., new lock type):**
- Header: `include/mcmini/model/objects/{name}.hpp` (define state machine)
- Transitions: `include/mcmini/model/transitions/{name}/{operation}.hpp` (one per operation)
- Implementation: `src/mcmini/model/transitions/{name}.cpp`
- Interception: `src/lib/wrappers.c` (add pthread_* wrapper)
- Registry: Register in transition registry callback table in `src/mcmini/mcmini.cpp`

**New Verification Algorithm:**
- Header: `include/mcmini/model_checking/algorithms/{name}.hpp`
- Implementation: `src/mcmini/model_checking/algorithms/{name}.cpp`
- Interface: Must inherit from `model_checking::algorithm`
- Entry: Call via `mcmini.cpp` orchestration

**New Test Case:**
- Source: `src/examples/{description}.c` (or `.cpp`)
- Purpose: Demonstrate feature or test case
- Build: Add to `src/examples/CMakeLists.txt`
- Run: Link with libmcmini.so and verify

**New Utility/Helper:**
- Location: `include/mcmini/misc/{purpose}.hpp`
- Pattern: Self-contained header if small, or header+source pair
- Namespace: `mcmini::` or utility-specific

**Process Source Strategy (fork vs DMTCP):**
- Header: `include/mcmini/real_world/process/{name}_process_source.hpp`
- Implementation: `src/mcmini/real_world/{name}_process_source.cpp`
- Interface: Inherit from `real_world::process_source`
- Factory: Add to process source selection logic in `mcmini.cpp`

## Special Directories

**include/dmtcp/:**
- Purpose: External DMTCP integration headers
- Generated: No (provided by DMTCP library)
- Committed: Checked in (vendored or symlinked)

**build/ and out/:**
- Purpose: Build artifacts
- Generated: Yes (CMake outputs)
- Committed: No (in `.gitignore`)

**.planning/codebase/:**
- Purpose: Codebase analysis documents (ARCHITECTURE.md, STRUCTURE.md, etc)
- Generated: Yes (produced by GSD analyzer)
- Committed: Yes (part of project documentation)

**.claude/:**
- Purpose: Claude Code configuration
- Generated: No (user-provided)
- Committed: Partially (settings.json yes, cache no)

---

*Structure analysis: 2026-08-08*
