<!-- refreshed: 2026-08-08 -->
# Architecture

**Analysis Date:** 2026-08-08

## System Overview

McMini is an explicit-state model checker for concurrent programs. It verifies multi-threaded C/C++ code by systematically exploring all possible thread interleavings using the Dynamic Partial Order Reduction (DPOR) algorithm. The system maintains an abstract model of the program while synchronizing it with actual process execution.

```text
┌─────────────────────────────────────────────────────────────────┐
│              Model Checking Algorithm (DPOR)                     │
│              `include/mcmini/model_checking/`                    │
│  Explores state space, manages backtracking, reports violations  │
└─────────────────────────────────────────┬───────────────────────┘
         │
         │ verify_using()
         ▼
┌─────────────────────────────────────────────────────────────────┐
│                 Coordinator (Tracer)                             │
│         `include/mcmini/coordinator/coordinator.hpp`             │
│  Synchronizes Model ↔ Process, discovers transitions dynamically │
└──────┬───────────────────────────┬──────────────────────────────┘
       │                           │
       │ maintains                 │ controls
       ▼                           ▼
┌────────────────────────┐  ┌──────────────────────────────────┐
│   Program Model        │  │   Real World Processes           │
│   `model/program.hpp`  │  │   `real_world/process.hpp`       │
│                        │  │                                  │
│ - Trace (sequence      │  │ - Proxy for running code         │
│   of transitions)      │  │ - Thread schedulable units       │
│ - State sequence       │  │ - IPC mailboxes for callbacks    │
│ - Pending transitions  │  │ - Process checkpointing (DMTCP)  │
│   (next ops per thread)│  │                                  │
└────────────────────────┘  └──────┬───────────────────────────┘
         │                          │
         │ mutates through          │ executes via
         ▼                          ▼
┌─────────────────────────────────────────────────────────────────┐
│         Visible Objects (State Model)                            │
│         `model/objects/` & `model/visible_object.hpp`            │
│                                                                  │
│  Mutexes, Semaphores, Condition Variables, Threads              │
│  Track inter-thread communication points                        │
└─────────────────────────────────────────────────────────────────┘
         │
         │ transitions applied via
         ▼
┌─────────────────────────────────────────────────────────────────┐
│         Injected Library (libmcmini.so)                          │
│         `src/lib/` and `include/mcmini/lib/`                    │
│                                                                  │
│  - Function interception (mutexes, threads, semaphores)         │
│  - Transition recording                                         │
│  - IPC communication with coordinator                           │
│  - Shared memory coordination                                   │
└─────────────────────────────────────────────────────────────────┘
```

## Component Responsibilities

| Component | Responsibility | File |
|-----------|----------------|------|
| Model Checker (DPOR) | Explore all program states, detect violations | `include/mcmini/model_checking/algorithms/classic_dpor.hpp` |
| Coordinator | Keep model and process synchronized | `include/mcmini/coordinator/coordinator.hpp` |
| Program | Abstract representation of execution trace and state | `include/mcmini/model/program.hpp` |
| State | Current state snapshot of all visible objects | `include/mcmini/model/state.hpp` |
| Transition | State transformation function (one-step operation) | `include/mcmini/model/transition.hpp` |
| Visible Object | Shared resource (mutex, semaphore, thread, cond var) | `include/mcmini/model/visible_object.hpp` |
| Real World Process | Proxy for actual running process | `include/mcmini/real_world/process.hpp` |
| Process Source | Factory for creating processes from checkpoint | `include/mcmini/real_world/process_source.hpp` |
| libmcmini.so | Injected library for function interception | `src/lib/` |

## Pattern Overview

**Overall:** Layered model-based verification engine with dynamic process synchronization

**Key Characteristics:**
- **Explicit-state model checking**: Constructs complete abstract model of all reachable states
- **DPOR algorithm**: Uses Flanagan-Godefroid DPOR to reduce exploration by 10-100x without losing correctness
- **Dynamic transition discovery**: Transitions discovered at runtime after execution, enabling accurate exploration of actual behavior
- **Checkpoint-based backtracking**: Uses DMTCP to create and restore process snapshots, enabling state space replay without re-execution
- **Thread-to-transition mapping**: Always tracks next immediate action for each thread; state model excludes process state

## Layers

**Algorithm Layer:**
- Purpose: Explores state space and detects violations (deadlock, data race, crash)
- Location: `include/mcmini/model_checking/`, `src/mcmini/model_checking/`
- Contains: DPOR algorithm implementation, reporter, statistics
- Depends on: Coordinator (to execute transitions and get state changes)
- Used by: Main verification orchestrator (via `mcmini.cpp`)

**Coordinator/Tracer Layer:**
- Purpose: Maintains one-to-one correspondence between abstract model and running process
- Location: `include/mcmini/coordinator/`, `src/mcmini/coordinator/`
- Contains: Stateful synchronization logic, dynamic transition discovery, object restoration
- Depends on: Model, Real World processes, Transition Registry
- Used by: Model Checking Algorithm (calls `execute_runner()`)

**Model Layer:**
- Purpose: Represents program history as trace + state sequence + pending transitions
- Location: `include/mcmini/model/`, `src/mcmini/model/`
- Contains: Program abstraction, state interface, transition interface, visible object definitions (mutex, thread, semaphore, condition variable)
- Depends on: None (foundation layer)
- Used by: Coordinator, Model Checking Algorithm

**Real World Layer:**
- Purpose: Bridge between abstract model and actual executing processes
- Location: `include/mcmini/real_world/`, `src/mcmini/real_world/`
- Contains: Process proxy, process source factory, checkpointing, IPC mailboxes, fork/DMTCP process strategies
- Depends on: Model (must understand process runner IDs and mailbox formats)
- Used by: Coordinator (to schedule threads and read execution results)

**Library Layer:**
- Purpose: Injected into target processes to intercept operations and record transitions
- Location: `src/lib/`, `include/mcmini/lib/`
- Contains: Function wrappers for pthreads, transition recording, IPC communication
- Depends on: Common layer (shared memory, mailbox format)
- Used by: Processes under verification (linked as libmcmini.so)

**Common Layer:**
- Purpose: Shared utilities used by both injected library and coordinator
- Location: `src/common/`, `include/mcmini/common/`
- Contains: Memory management, exit handling, shared memory configuration, mailbox IPC
- Depends on: None
- Used by: Library layer and some Real World components

## Data Flow

### Primary Request Path (Model Checking Loop)

1. **Initialize** (`src/mcmini/mcmini.cpp` ~line 100-200)
   - Create initial model from process startup
   - Register all transition types in registry
   - Instantiate DPOR algorithm and coordinator

2. **Select Next Transition** (`src/mcmini/model_checking/algorithms/classic_dpor.cpp` ~line 150-300)
   - DPOR algorithm examines pending transitions
   - Chooses next runner to execute based on backtrack sets and dependency relations
   - Returns runner ID to coordinator

3. **Execute Transition** (`src/mcmini/coordinator/coordinator.cpp` ~line 37-100)
   - Call `execute_runner(runner_id)` on current process handle
   - Process resumes thread at signal breakpoint
   - Thread executes next operation (e.g., `pthread_mutex_lock`)
   - Interception hook in libmcmini.so captures it
   - Writes transition info to mailbox, thread blocks

4. **Discover Transition** (`src/mcmini/coordinator/coordinator.cpp` ~line 80-150)
   - Coordinator reads mailbox from stopped thread
   - Looks up callback for transition type in registry
   - Callback reconstructs transition object from mailbox data
   - Passes remote memory mapping to callback for address translation

5. **Update Model** (`src/mcmini/coordinator/coordinator.cpp` ~line 150-200)
   - Apply transition to current program model (state + trace)
   - Transition transforms state and appends to trace
   - Extract newly visible operations (pending transitions)
   - Discover new runners (threads) if created

6. **Report Results** (`include/mcmini/model_checking/algorithm.hpp` ~line 30-45)
   - On deadlock: No enabled transitions at state
   - On data race: Race detected in state model
   - On crash: Process termination detected
   - On successful state: Algorithm continues exploration

### Backtracking Flow (State Space Replay)

1. **Backtrack Decision** (`src/mcmini/model_checking/algorithms/classic_dpor.cpp` ~line 200-250)
   - Algorithm determines backtrack point from dependency relations
   - Needs to replay up to state N with different thread choice
   - Calls coordinator's `return_to_depth(N)`

2. **Checkpoint Restoration** (`src/mcmini/real_world/dmtcp_process_source.cpp`)
   - Process source has DMTCP checkpoint at depth N
   - Spawns new process from checkpoint (via DMTCP coordinator)
   - New process starts at depth N + 1

3. **Model Rewind** (`src/mcmini/coordinator/coordinator.cpp`)
   - Coordinator rewinds program model to depth N
   - Slices state sequence and trace to N states
   - Clears pending transitions
   - Re-discovers first N+1 transitions from new process

4. **Resume Exploration** (Back to step 2 of Primary Path)
   - Algorithm schedules different runner at depth N
   - Continues forward exploration with new interleaving

**State Management:**
- State is immutable: transitions produce new states without modifying old ones
- State sequence stores all states S_0, S_1, ..., S_N reached along trace
- Visible objects maintain history of all states they've passed through
- Process state (memory) is separate from model state; only forward execution possible

## Key Abstractions

**Program (`model::program`):**
- Purpose: Container capturing program history and next operations
- Comprises: Trace (sequence of transitions), State sequence (S_0...S_N), Pending transitions (next op per thread)
- Pattern: Immutable history + mutable current state snapshot
- Implementation: `include/mcmini/model/program.hpp`, `src/mcmini/model/program.cpp`

**Transition (`model::transition`):**
- Purpose: Pure function representing one atomic step (e.g., pthread_mutex_lock)
- Formal definition: Partial function Σ → Σ (state to state)
- Key distinction: May exist in state but not be enabled; executor thread determines actual execution
- Concrete subclasses: Mutex operations, thread operations, semaphore operations, condition variable operations
- Examples: `include/mcmini/model/transitions/mutex/mutex_lock.hpp`, `include/mcmini/model/transitions/thread/thread_create.hpp`

**Visible Object (`model::visible_object`):**
- Purpose: Represents shared resource with evolution history
- Contains: Vector of states showing how object changed (S_0, S_1, ..., S_N)
- Rationale: Necessary for understanding inter-thread communication and state coverage
- Concrete types: Mutex, Semaphore, Condition variable, Thread
- Pattern: Each state implements `visible_object_state` interface with `clone()`, `to_string()`, equality

**State (`model::state`):**
- Purpose: Snapshot of all visible objects at one point in trace
- Interface: Read-only queries (get object state, runner state, count)
- Mutable variant: `mutable_state` for adding objects and runners
- Implementation: `model/state/diff_state.hpp` (stores only differences from previous state)

**Visible Object State (`model::visible_object_state`):**
- Purpose: Immutable snapshot of one resource's state (e.g., mutex locked/unlocked/destroyed)
- Each concrete type defines its state enum: `mutex::state`, `thread::state`, `semaphore::state`
- Support: `clone()` for creating copies, `to_string()` for debugging

**Process (`real_world::process`):**
- Purpose: Proxy for actual running process; forward iterator for execution
- Operations: `execute_runner(id)` to run thread, returns mailbox with results
- Properties: No backward execution possible (matches real process behavior), contains runners
- Implementations: `local_linux_process.hpp` (fork), `dmtcp_process.hpp` (DMTCP checkpointing)

## Entry Points

**Main Verification (`src/mcmini/mcmini.cpp`):**
- Location: `src/mcmini/mcmini.cpp` ~line 50-150
- Triggers: Called by user verification code via `mcmini::verify()` or `mcmini::main()`
- Responsibilities:
  - Initialize process source (fork-based or DMTCP-based)
  - Create initial program model from startup state
  - Instantiate DPOR algorithm
  - Loop: algorithm selects runner → coordinator executes → model updates

**Thread Interception (`src/lib/interception.c`):**
- Location: `src/lib/interception.c` ~line 50-300
- Triggers: When target process calls pthreads operations (pthread_create, pthread_mutex_lock, etc.)
- Responsibilities:
  - Capture call parameters
  - Serialize transition info
  - Write to shared mailbox
  - Signal pause point for coordinator to read

**Process Source Creation:**
- Fork-based: `src/mcmini/real_world/fork_process_source.cpp` (uses fork() to spawn)
- DMTCP-based: `src/mcmini/real_world/dmtcp_process_source.cpp` (uses DMTCP coordinator for checkpoints)

## Architectural Constraints

- **Threading:** Single-threaded coordinator; processes under test are multi-threaded but paused at interception points
- **Global state:**
  - `src/lib/main.c`: `global_shm_start` (shared memory region pointer)
  - Model checkpoint caches in process source
  - Transition registry in coordinator (maps runtime type IDs to callbacks)
- **Circular imports:** None (clean layering enforced)
- **Process state separation:** Model state and process memory state are completely separate; model state excludes process state per design
- **Transition atomicity:** Each transition represents one atomic operation; transitions do NOT spawn new states incrementally
- **Clock vectors:** Used by DPOR to track causality; stored in algorithm's stack items, not in model

## Anti-Patterns

### Defining Transitions With Process State Knowledge

**What happens:** A transition implementation tries to check process memory to determine if it's enabled
**Why it's wrong:** Transitions should be defined in state but their enablement determined by pending transitions; process state is unknown until after execution
**Do this instead:** Transitions are pure state functions; `model::program` maintains pending_transitions mapping that captures "is this enabled now?"

### Modifying States In-Place

**What happens:** Code mutates state objects after they're stored in history
**Why it's wrong:** DPOR algorithm and backtracking depend on immutable state snapshots; modifications corrupt previous states
**Do this instead:** Transitions produce new state objects via `state->mutable_clone()` and `.freeze()`; old states remain unchanged

### Direct Memory Access Across Process Boundaries

**What happens:** Coordinator reads process memory directly instead of using mailbox
**Why it's wrong:** Race conditions with process execution; address space layout changes after checkpoint restore
**Do this instead:** All inter-process communication goes through signed mailbox protocol; addresses translated via `model_to_system_map` callback parameter

### Assuming Linear Program Flow

**What happens:** Code assumes trace order matches execution order without DPOR backtracking
**Why it's wrong:** DPOR explores different interleavings; same thread may execute same code in multiple states
**Do this instead:** Parameterize DPOR vs linear mode; when linear, can cache transitions; when DPOR, must rediscover

## Error Handling

**Strategy:** Exceptions for configuration/setup errors; callbacks for runtime violations

**Patterns:**
- Configuration errors throw `std::runtime_error` (process creation failure, transition registry mismatch)
- Verification violations invoked via callbacks: `callbacks::deadlock()`, `callbacks::data_race()`, `callbacks::crash()`
- Process errors: `real_world::process::execution_error` (runner not found, process unresponsive)
- Model violations: `model::undefined_behavior_exception` (raised by transition validation)

## Cross-Cutting Concerns

**Logging:**
- Facility: `logging::logger` in `include/mcmini/log/logger.hpp`
- Pattern: Create logger per module (e.g., `logging::logger dpor_logger("dpor");`)
- Levels: Controlled via `LogControl` with severity filters
- Usage: `log_debug(logger) << "message" << logging::severity_level::verbose;`

**Validation:**
- Per-transition: Each transition subclass validates preconditions and state consistency
- Per-state: State implementation validates object IDs and runner IDs exist
- At coordinator: Checks that pending transitions align with enabled runners before execution

**Authentication:** None (assumes trusted process environment; DMTCP integration via plugin)

---

*Architecture analysis: 2026-08-08*
