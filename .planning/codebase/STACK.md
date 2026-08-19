# Technology Stack

**Analysis Date:** 2026-08-08

## Languages

**Primary:**
- C11 - Core system interfaces and low-level process management (`src/common/`, `src/lib/`)
- C++11 - Model checker logic and high-level abstractions (`src/mcmini/`)

**Secondary:**
- Python - Debugging scripts for GDB integration (`script/debug-mcmini-child.py`, `script/debug-mcmini-dmtcp.py`)

## Runtime

**Environment:**
- Linux (x86_64) - Required for process spawning, signal handling, and POSIX thread support
- Kernel must support: signals, processes, threads, ptrace (process tracing)

**Platform Requirements:**
- POSIX-compliant system (Linux primary target)
- Support for dynamic library loading (`dlopen`, `dlsym`)
- Support for shared memory (`shm_open`, `shm_unlink`)

## Build System

**Primary:**
- CMake 3.10+ - Project configuration and compilation
  - Minimum required: 3.23 (for presets support)
  - Config files: `CMakeLists.txt`, `CMakePresets.json`

**Build Generator:**
- Unix Makefiles - Default build system
- Supports Debug and Release configurations

**Build Artifacts:**
- `libmcmini.so` - Shared library injected into target processes
- `mcmini` - Main model checker executable
- Example binaries in `out/system-*/bin/`

## Key Dependencies

**System Libraries (Linked):**
- `libpthread` - POSIX thread management (-pthread)
- `librt` - Real-time library for shared memory operations (-lrt)
- `libm` - Math library (-lm)
- `libdl` - Dynamic linking library (-ldl)

**Optional External:**
- SCIP - Linear/mixed-integer optimization (optional, controlled by `MCMINI_USE_SCIP` CMake flag)
  - When enabled: linked to main `mcmini` executable
  - Location: managed by CMake `find_package(scip)`

**Package Manager:**
- vcpkg (optional) - C++ dependency management
  - Used when `CMAKE_TOOLCHAIN_FILE` points to `${VCPKG_ROOT}/scripts/buildsystems/vcpkg.cmake`
  - Environment: `VCPKG_ROOT`, `VCPKG_DISABLE_METRICS=1`
  - Not required for basic builds (see `no-vcpkg-*` presets)

## Build Configuration

**Environment Variables:**
- `VCPKG_ROOT` - Path to vcpkg installation (optional)
- `VCPKG_DISABLE_METRICS=1` - Disable vcpkg telemetry (if using vcpkg)
- `CMAKE_EXPORT_COMPILE_COMMANDS=ON` - Generate compile_commands.json for IDE integration

**Build Presets:**
- `debug` / `no-vcpkg-debug` - Debug build with symbols
- `release` / `no-vcpkg-release` - Optimized release build
- Build jobs: 2 (parallel compilation limit in presets)

**CMake Flags:**
- `BUILD_TESTS=ON` - Enable test building
- `VERBOSE_TESTING=OFF` - Disable verbose test output
- `MCMINI_USE_SCIP=OFF` - SCIP optimization support (default off)
- `CMAKE_BUILD_TYPE` - Debug or Release
- `CMAKE_C_STANDARD=11` - C standard requirement
- `CMAKE_CXX_STANDARD=11` - C++ standard requirement

## Development Tools

**Code Formatting:**
- clang-format - C/C++ code formatter
  - Config: `.clang-format`
  - Style: Google C++ style with custom rules
  - Line length: 80 characters (default)

**Code Analysis:**
- clang-tidy - Static analysis tool
  - Config: `.clang-tidy`
  - Checks: clang-diagnostic-*, clang-analyzer-*
  - Extensions recognized: .h, .hpp, .hh, .hxx (headers); .c, .cpp, .cc, .cxx (implementation)

**Pre-commit Hooks:**
- pre-commit framework v4.3.0
  - Checks: large-files, case-conflicts, symlinks, trailing-whitespace, end-of-file-fixer
  - Fail-fast: enabled (stops on first error)

## Compiler Flags

**Common:**
- `-Wall` - Enable all common warnings

**libmcmini (shared library):**
- `-Wall -Werror` - Treat warnings as errors
- `-fPIC` - Position-independent code (required for shared libraries)

**Linking Flags:**
- Main executable: `-lrt -pthread`
- Shared library: `-lrt -pthread -lm -ldl`

## Compiler Specifications

**C Compiler:** GCC or Clang (standard Unix toolchain)
- C11 support required
- Tested on: GCC 9+ (inferred from -Wall flags)

**C++ Compiler:** G++ or Clang++
- C++11 support required
- Tested on: G++ 9+ (inferred from standard library usage)

---

*Stack analysis: 2026-08-08*
