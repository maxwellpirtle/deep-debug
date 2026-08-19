# Testing Patterns

**Analysis Date:** 2026-08-08

## Test Framework

**Current State:**
- No formal test framework configured (CTest/scripting not yet implemented)
- Test TODO: `test/CMakeLists.txt` contains comment: "TODO: Add Ctest/scripting capabilities to quickly run tests"
- Tests are C/C++ programs compiled as standalone executables

**Test Execution:**
- Tests are model-checking test cases: programs to be verified by McMini model checker
- Not traditional unit tests but rather concurrency test cases demonstrating bugs and race conditions
- Tests are run manually or through McMini's model checking process

**Assertion Method:**
- C: `assert()` from `<assert.h>`
- C++: Custom `asserts` class from `include/mcmini/misc/asserts.hpp`

## Test File Organization

**Location:**
- Test directory: `test/` (co-located with source at repository root)
- Subdirectories by test category: `test/assertions/`, `test/segfaults/`

**Naming Convention:**
- C test files: `*.c`
- C++ test files: `.cpp`
- Descriptive names: `assertion-failure.c`, `philosophers_template_fails.cpp`, `philosophers_branch_fails.cpp`
- File name indicates what is being tested

**Structure:**
```
test/
├── CMakeLists.txt          # Build configuration (not yet enabled)
├── assertions/
│   └── assertion-failure.c # Test case: race condition with assertions
└── segfaults/
    ├── philosophers_template_fails.cpp
    └── philosophers_branch_fails.cpp
```

## Test Structure

**Typical Test Pattern:**
```c
#include <assert.h>
#include <pthread.h>
#include <stdio.h>

// Global state
int global_var = 0;
pthread_mutex_t lock;

// Thread functions
void *thread_function(void *arg) {
    // Concurrent operations
    pthread_mutex_lock(&lock);
    int var = global_var;
    pthread_mutex_unlock(&lock);

    if (!var) {
        // Modify state
        pthread_mutex_lock(&lock);
        global_var = 1;
        pthread_mutex_unlock(&lock);
    }
    return NULL;
}

int main() {
    pthread_t tid1, tid2;

    // Create threads
    pthread_create(&tid1, NULL, thread_function, NULL);
    pthread_create(&tid2, NULL, thread_function, NULL);

    // Join threads
    pthread_join(tid1, NULL);
    pthread_join(tid2, NULL);

    // Assert expected outcome (may fail due to race condition)
    assert(global_var_thread1 ^ global_var_thread2);

    return 0;
}
```

**Key Elements:**
- Global variables to capture state mutations
- Multiple threads interacting on shared state
- Synchronization primitives (mutexes, condition variables, semaphores)
- Assert statements to verify expected or reveal unexpected behavior
- Test cases designed to be model-checked by McMini

**Test Categories:**

| Category | Purpose | Location | Example |
|----------|---------|----------|---------|
| Assertions | Test assertion violations and race conditions | `test/assertions/` | `assertion-failure.c` tests XOR condition |
| Segfaults | Test segmentation faults and deadlocks | `test/segfaults/` | `philosophers_template_fails.cpp` |

## Mocking

**Framework:** Not detected - not applicable

**Approach:**
- Tests are integration-level: run entire programs under McMini
- No mocking needed; concurrency is real (controlled by model checker scheduler)
- Thread synchronization uses real pthreads primitives
- I/O and system calls recorded and replayed by McMini

**No Mock Objects:**
- All interactions with pthreads are real
- All interactions with synchronization primitives are real
- Test programs are "pure" with no external dependencies

## Fixtures and Factories

**Test Data:**
- Global variables initialized at compile-time or in `main()`
- Example: `pthread_mutex_t lock_global_variables` initialized globally
- No factory pattern observed in tests

**Location:**
- Fixtures defined inline in test files
- State initialization at start of `main()`
- Thread creation in `main()`

**Example Setup:**
```c
int main() {
    int NUM_THREADS = 3;
    pthread_t thread[NUM_THREADS];
    pthread_mutex_t mutex_resource[NUM_THREADS];

    for (i = 0; i < NUM_THREADS; i++) {
        pthread_mutex_init(&mutex_resource[i], NULL);
        // ... setup thread arguments
    }
}
```

## Coverage

**Requirements:** Not enforced

**Tools:** No coverage tools detected or configured

**Approach:**
- Model-checking coverage: all possible interleavings explored
- Execution coverage not traditionally measured for these tests
- Focus: finding bugs through exhaustive scheduling exploration

## Test Types

**Model Checking Tests:**
- **Scope:** Full program execution under controlled scheduler
- **Approach:** McMini explores all (or significant) thread interleavings
- **Goal:** Find race conditions, deadlocks, assertion violations
- **Example:** `test/assertions/assertion-failure.c` - checks if assertion holds under all schedules

**Concurrency Tests:**
- **Scope:** Multiple threads with shared state
- **Approach:** Threads synchronize using pthreads primitives (mutex, condition variable, semaphore)
- **Goal:** Verify correctness under concurrent access patterns
- **Example:** `test/segfaults/philosophers_template_fails.cpp` - dining philosophers problem

**Assertion Tests:**
- **Scope:** Programs with explicit assertions
- **Approach:** Program terminates with assertion failure if condition violated
- **Goal:** Catch violated invariants
- **Example:** `assert(global_var_thread1 ^ global_var_thread2)` - exactly one should be true

**Deadlock/Livelock Tests:**
- **Scope:** Programs that can deadlock under bad interleavings
- **Approach:** McMini explores scheduler behaviors
- **Goal:** Verify no deadlock or demonstrate it
- **Example:** `test/segfaults/philosophers_template_fails.cpp` - naive implementation deadlocks

## Async Testing

**Approach:**
- No async/await patterns (C/pthreads model)
- Concurrency via `pthread_create()` and `pthread_join()`
- No promise/future abstractions

**Example:**
```c
pthread_t tid;
pthread_create(&tid, NULL, thread_function, NULL);
pthread_join(tid, NULL);  // Wait for completion
```

## Error Testing

**Patterns:**
- Assertion failure: termination with exit code != 0
- Signal handling: signals captured and logged
- Synchronization errors: deadlock detected by timeout or model checker

**Detecting Test Failures:**
- Assertion failure: `assert()` triggers `SIGABRT` → process exit
- Program crash: segfault, bus error, etc. → process exit
- Model checker detection: McMini explores all interleavings and reports bugs

**Example Error Test:**
```c
// BUG comment marks intentional race condition
// BUG: Check without proper synchronization
pthread_mutex_lock(&lock);
int var = global_var;
pthread_mutex_unlock(&lock);

if (!var) {
    // Another thread might have changed global_var between check and set
    pthread_mutex_lock(&lock);
    global_var = 1;
    pthread_mutex_unlock(&lock);
}
```

## Running Tests

**Manual Build:**
```bash
cd /home/parallels/deep-debug
cmake -B build
cd build
make
```

**Manual Execution:**
- Test programs are in `build/` after compilation
- Run with McMini: `./mcmini ./test_program`
- Run standalone: `./test_program` (may not trigger bugs without scheduler control)

**CI/CD:** Not yet configured (TODO in test/CMakeLists.txt)

## Known Issues

**Testing Limitations:**
- No automated test runner (CTest/scripting not implemented)
- No CI/CD integration
- No coverage measurement
- Tests must be manually curated and run
- Test execution depends on McMini model checker for correctness verification

**Future Work:**
- Add CTest configuration to enable `ctest` command
- Add test scripts for automated execution
- Add model checking result parsing and reporting
- Extend test coverage with more concurrency scenarios

## Test Development Guidelines

**When Adding Tests:**
1. Create in appropriate category directory: `test/assertions/` or `test/segfaults/`
2. Use descriptive filename: `test/<category>/<what_is_tested>.c`
3. Include `#include <assert.h>` and `#include <pthread.h>`
4. Initialize global state at file or function scope
5. Create threads in `main()` using `pthread_create()`
6. Join threads using `pthread_join()`
7. Add assertion at end to verify expected behavior
8. Use `// BUG:` comments to mark known issues being tested
9. Use `// NOTE:` comments to explain non-obvious behavior
10. Compile with project build system (CMake)
11. Run under McMini: `mcmini ./program` to verify model checking finds issues

**Test Code Style:**
- Follow CONVENTIONS.md for C/C++ style
- Keep test functions small and focused
- Use descriptive printf() statements for debugging
- Avoid external dependencies (only pthread and standard library)
- Mark expected failures with comments

---

*Testing analysis: 2026-08-08*
