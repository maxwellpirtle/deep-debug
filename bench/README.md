# McMini Benchmark Suite

Eight fixed measurement instruments — one bug-carrying and one known-clean program for each of
four synchronization patterns: mutex-only, semaphore-only, condition-variable, and mixed.

| | bug-carrying | clean |
|---|---|---|
| mutex | `mutex-bug` | `mutex-clean` |
| semaphore | `sem-bug` | `sem-clean` |
| condition variable | `cv-bug` | `cv-clean` |
| mixed | `mixed-bug` | `mixed-clean` |

**These programs must stay fixed for the milestone.** Editing one invalidates its row in the
checked-in baseline, and every speed claim measured against that row. That is why they live here
and not in `src/examples/`, which is documentation and gets edited freely. Every program scales
genuinely with `--threads=N` — none clamps or ignores the flag.

## Run the suite

```sh
sh script/run-bench.sh --build-dir build-release
```

One run per program, the 13-column TSV result set on stdout. `run` is the default subcommand.

The build directory must hold `mcmini`, `libmcmini.so` and all eight programs side by side.
McMini computes `LD_PRELOAD` as `dirname(<target>)/libmcmini.so`, so a program that is not
co-located with the `.so` dies before model checking starts.

### Flags

| Flag | Default | Environment variable | Meaning |
|---|---|---|---|
| `--build-dir DIR` | `build` | `BENCH_BUILD_DIR` | Directory holding `mcmini`, `libmcmini.so` and the eight programs |
| `--threads N` | `3` | `BENCH_THREADS` | Thread count passed to each program |
| `--timeout SECONDS` | `120` | `BENCH_TIMEOUT_SECONDS` | Per-program wall-clock budget; an overrun is recorded as `status=timeout` |
| `--repeat N` | `1` | `BENCH_REPEAT` | Run each program N times and report the median of both timings |
| `--out FILE` | stdout | — | Write the result set to `FILE`; its parent directory must already exist |
| `--force` | off | — | Permit an `--out` write inside `bench/baseline/` |

For an even `--repeat N` the median is the lower of the two middle observations, never their
average, so every reported number is a value the machine actually produced. Traces, transitions,
violation kinds and the exhaustion flag are deterministic and are asserted identical across the N
runs; a program whose deterministic columns move is reported `status=error` rather than measured.

### Columns

| # | Column | Meaning |
|---|---|---|
| 1 | `program` | Benchmark name; row order is fixed, so two result files stay aligned line for line |
| 2 | `threads` | Thread count the program ran with |
| 3 | `traces` | Interleavings McMini explored |
| 4 | `transitions` | Synchronization operations executed across all traces |
| 5 | `violation_kinds` | Comma-separated kinds reported, alphabetical, or `-` |
| 6 | `violation_counts` | `kind:count` per reported kind, or `-` |
| 7 | `exhausted` | `yes` when the state space was searched to completion |
| 8 | `max_depth_per_thread` | Per-thread depth limit in effect |
| 9 | `max_depth_per_trace` | Per-trace depth limit in effect |
| 10 | `transition_ceiling` | Compile-time transition ceiling in effect |
| 11 | `elapsed_ms` | End-to-end wall clock measured by the runner, including process startup |
| 12 | `check_ms` | Model-checking duration measured by McMini around its own loop |
| 13 | `status` | `ok`, `timeout`, or `error` |

Every program always produces exactly one row. A missing binary, a crash and a timeout all become
rows with `status=error` or `status=timeout` and every McMini-sourced column rendered `-`.

The suite exits non-zero only on harness failure. Violations McMini reports are data in the result
set, never an exit code — the suite deliberately contains buggy programs.

## Check that the programs still scale

```sh
sh script/run-bench.sh scaling --build-dir build-release
```

Runs every program at `--threads=2` and again at `--threads=3` and reports `SCALES`, `FROZEN` or
`UNMEASURED`, exiting 1 on anything but `SCALES`. A program reporting the same transition count at
both thread counts is ignoring its thread flag, and its measurements mean nothing.

## Re-capture the baseline

`bench/baseline/baseline-release.tsv` is the milestone's fixed pre-optimization reference. It was
produced by exactly this command:

```sh
cmake -S . -B build-release -DCMAKE_BUILD_TYPE=Release -DBUILD_TESTS=YES
cmake --build build-release -j2
sh script/run-bench.sh scaling --build-dir build-release
sh script/run-bench.sh --build-dir build-release --threads 3 --repeat 5 \
    --out bench/baseline/baseline-release.tsv --force
```

Release is the canonical baseline build: the milestone's premise is a claim about optimized
builds, and Debug timings are dominated by unoptimized code.

`--force` is required because the runner refuses to write inside `bench/baseline/` without it.

The capture is then prefixed by hand with a `#`-prefixed header block, one `key=value` per line,
above the column header:

```
# mcmini-bench-baseline v1
# commit=<git rev-parse HEAD>
# build_type=Release
# compiler=<first line of `cc --version`>
# cpu=<CPU description>
# threads=3
# repeats=5
# timeout_seconds=120
# captured=<ISO 8601 UTC timestamp>
```

`compare` reads exactly these keys. Both `run` output and `compare` input tolerate `#` lines.

## Compare a run against the baseline

```sh
sh script/run-bench.sh --build-dir build-release --out /tmp/current.tsv
sh script/run-bench.sh compare bench/baseline/baseline-release.tsv /tmp/current.tsv
```

`compare` reads two files and spawns nothing, so it needs no build tree. It exits 0 whatever it
finds, and 1 only on harness failure.

Reading the output:

- **`MATCH`** — `traces`, `transitions` and `violation_kinds` are identical. These are
  deterministic; a fresh run at the same commit and thread count must agree with the baseline on
  all three.
- **`CHANGED`** — at least one of those three moved, with the before and after appended
  (`traces=A->B`). `violation_counts` is informational and never on its own makes a program
  `CHANGED`.
- **`TRUNCATED`** — `exhausted` is `no` on one side or the other.
- **`MISSING` / `EXTRA`** — the program is in one file and not the other.
- **`elapsed=` / `check=`** — current over baseline, to two decimal places. These always move a
  little, which is why `compare` exists rather than `diff`. The pair distinguishes a real
  model-checking win from constant process-startup cost.
- **`WARNING:` on stderr** — a header-block field differs between the two files: commit, build
  type, compiler, CPU, thread count or repeat count. Wall clock across Debug and Release differs
  by more than any optimization in this milestone, so a ratio quoted across a warning is not a
  result. A run captured with the default `--repeat 1` against the `--repeat 5` baseline warns on
  `repeats`, which is expected.
- **`SUMMARY`** — the machine-readable last line:
  `SUMMARY programs=N kinds_changed=N traces_changed=N truncated=N`.

## The rule that keeps the instrument honest

A row that is not `status=ok` with `exhausted=yes` is not a measurement, and no speed claim may be
made from it — a truncated search records fewer traces and less time, which is indistinguishable
from a speedup.
