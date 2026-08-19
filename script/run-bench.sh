#!/bin/sh
#
# Run the McMini benchmark suite and emit one tab-separated row per program.
#
#   sh script/run-bench.sh [run] [--build-dir DIR] [--threads N]
#                          [--timeout SECONDS] [--repeat N] [--out FILE] [--force]
#   sh script/run-bench.sh compare BASELINE CURRENT
#   sh script/run-bench.sh scaling [--build-dir DIR] [--timeout SECONDS]
#
# Only the TSV result set reaches stdout. McMini writes a full trace dump on
# every violating trace, so each invocation's output is redirected into a
# temporary directory: an unredirected run would interleave trace dumps into
# the result set and load the wall-clock number with trace-dump I/O.

set -eu

build_dir="${BENCH_BUILD_DIR:-build}"
threads="${BENCH_THREADS:-3}"
timeout_seconds="${BENCH_TIMEOUT_SECONDS:-120}"
repeat="${BENCH_REPEAT:-1}"

# Row order follows this list and never varies, so two result files stay
# aligned line for line.
PROGRAMS="mutex-bug mutex-clean sem-bug sem-clean cv-bug cv-clean mixed-bug mixed-clean"

# Alphabetical, not observation order: the same bug set must always render to
# the same string so a comparison can be a string equality.
VIOLATION_KINDS="abnormal_termination deadlock nonzero_exit_code undefined_behavior"

# Every column a repeated run must reproduce exactly. Only the two timings may
# legitimately move between repetitions.
DETERMINISTIC_COLUMNS="traces transitions violation_kinds violation_counts exhausted max_depth_per_thread max_depth_per_trace transition_ceiling"

# The single character standing in for every McMini-sourced column on a row
# whose run did not produce a record.
DASH="-"

# The one write target that is a checked-in repository artifact.
BASELINE_DIR="bench/baseline"

header_line() {
  printf 'program\tthreads\ttraces\ttransitions\tviolation_kinds\tviolation_counts\texhausted\tmax_depth_per_thread\tmax_depth_per_trace\ttransition_ceiling\telapsed_ms\tcheck_ms\tstatus\n'
}

usage() {
  cat <<EOF
Usage: run-bench.sh [run] [--build-dir DIR] [--threads N] [--timeout SECONDS]
                          [--repeat N] [--out FILE] [--force] [--help]
       run-bench.sh compare BASELINE CURRENT
       run-bench.sh scaling [--build-dir DIR] [--timeout SECONDS]

Subcommands:
  run       Measure every program once and emit the 13-column result set.
            This is the default when no subcommand is given.
  compare   Read two result files and report per-program deltas. traces,
            transitions and violation_kinds are must-match-or-explain;
            violation_counts is informational and never on its own makes a
            program CHANGED; the two timings are reported as ratios of current
            over baseline. A row whose exhausted flag is 'no' on either side is
            marked TRUNCATED, because a truncated search is indistinguishable
            from a speedup. Ends with a machine-readable SUMMARY line. Exits 0
            whatever it finds and 1 only on harness failure.
  scaling   Run every program at --threads=2 and again at --threads=3 and exit
            1, naming the program, when any reports the same transition count
            at both. Catches a program that silently ignores its thread flag.

  --build-dir DIR    Directory holding mcmini, libmcmini.so and every benchmark
                     binary (default: build; also BENCH_BUILD_DIR).
  --threads N        Thread count passed to each benchmark program
                     (default: 3; also BENCH_THREADS).
  --timeout SECONDS  Per-program wall-clock budget. A run that exceeds it is
                     killed and recorded as status=timeout
                     (effective: ${timeout_seconds}; also BENCH_TIMEOUT_SECONDS).
  --repeat N         Run each program N times and report the MEDIAN of both
                     timings (effective: ${repeat}; also BENCH_REPEAT). Traces,
                     transitions, violation kinds and the exhaustion flag are
                     deterministic and are asserted identical across the N
                     runs; a program whose deterministic columns move is
                     reported as status=error rather than measured.
                     For an even N the median is the LOWER of the two middle
                     observations, never their average, so every reported
                     number is a value the machine actually produced.
  --out FILE         Write the result set to FILE instead of stdout. FILE's
                     parent directory must already exist; the runner creates no
                     directory trees. A FILE inside ${BASELINE_DIR}/ is refused
                     without --force.
  --force            Permit an --out write inside ${BASELINE_DIR}/.

Programs, in row order:
  ${PROGRAMS}

Every program always produces exactly one row; a timeout, a crash or a missing
binary becomes a status=timeout or status=error row rather than a missing one.
Exit status is 0 when every row is status=ok and 1 on harness failure.
Violations McMini reports are data in the result set, never an exit code.
EOF
}

require_value() {
  if [ "$2" -lt 2 ]; then
    printf 'run-bench: %s requires a value\n' "$1" >&2
    exit 1
  fi
}

require_positive_integer() {
  case "$2" in
    "" | *[!0-9]*)
      printf 'run-bench: %s expects a positive integer, got: %s\n' "$1" "$2" >&2
      exit 1
      ;;
  esac
  if [ "$2" -lt 1 ]; then
    printf 'run-bench: %s expects a positive integer, got: %s\n' "$1" "$2" >&2
    exit 1
  fi
}

want_help=no
out_path=""
force=no
compare_baseline=""
compare_current=""

# A bare invocation stays one word: no subcommand means `run`.
subcommand=run
case "${1:-}" in
  run | compare | scaling)
    subcommand="$1"
    shift
    ;;
esac

while [ $# -gt 0 ]; do
  case "$1" in
    --build-dir)
      require_value "$1" $#
      build_dir="$2"
      shift 2
      ;;
    --threads)
      require_value "$1" $#
      threads="$2"
      shift 2
      ;;
    --timeout)
      require_value "$1" $#
      timeout_seconds="$2"
      shift 2
      ;;
    --repeat)
      require_value "$1" $#
      repeat="$2"
      shift 2
      ;;
    --out)
      require_value "$1" $#
      out_path="$2"
      shift 2
      ;;
    --force)
      force=yes
      shift
      ;;
    --help | -h)
      want_help=yes
      shift
      ;;
    -*)
      printf 'run-bench: unrecognized option: %s\n' "$1" >&2
      usage >&2
      exit 1
      ;;
    *)
      if [ "$subcommand" = compare ] && [ -z "$compare_baseline" ]; then
        compare_baseline="$1"
      elif [ "$subcommand" = compare ] && [ -z "$compare_current" ]; then
        compare_current="$1"
      else
        printf 'run-bench: unexpected argument: %s\n' "$1" >&2
        usage >&2
        exit 1
      fi
      shift
      ;;
  esac
done

if [ "$want_help" = yes ]; then
  usage
  exit 0
fi

if [ "$subcommand" = compare ] && { [ -z "$compare_baseline" ] || [ -z "$compare_current" ]; }; then
  printf 'run-bench: compare needs a BASELINE and a CURRENT result file\n' >&2
  exit 1
fi

require_positive_integer --threads "$threads"
require_positive_integer --timeout "$timeout_seconds"
require_positive_integer --repeat "$repeat"

# The checked-in baseline is the milestone's only pre-optimization record: once
# Phase 2 lands, the commit it was taken at is no longer reproducible from the
# working tree. An accidental redirect must not be able to destroy it.
if [ -n "$out_path" ]; then
  out_dir=$(dirname -- "$out_path")
  if [ -d "$out_dir" ]; then
    resolved_out_dir=$(cd "$out_dir" && pwd -P)
  else
    resolved_out_dir="$out_dir"
  fi
  case "$resolved_out_dir" in
    "$BASELINE_DIR" | "$BASELINE_DIR"/* | */"$BASELINE_DIR" | */"$BASELINE_DIR"/*)
      if [ "$force" != yes ]; then
        printf 'run-bench: refusing to write inside %s/ without --force: %s\n' \
          "$BASELINE_DIR" "$out_path" >&2
        exit 1
      fi
      ;;
  esac
  if [ ! -d "$out_dir" ]; then
    printf 'run-bench: output directory does not exist: %s\n' "$out_dir" >&2
    exit 1
  fi
fi

# compare reads files and spawns nothing, so it must not require a build tree.
if [ "$subcommand" != compare ]; then
  if [ ! -d "$build_dir" ]; then
    printf 'run-bench: build directory not found: %s\n' "$build_dir" >&2
    exit 1
  fi

  # McMini computes LD_PRELOAD as dirname(<target>)/libmcmini.so, so a build
  # directory without the .so next to the programs turns every row into an
  # error for a reason that has nothing to do with the programs. Catch it once.
  for required in mcmini libmcmini.so; do
    if [ ! -f "$build_dir/$required" ]; then
      printf 'run-bench: %s not found in %s\n' "$required" "$build_dir" >&2
      exit 1
    fi
  done
fi

tmpdir=$(mktemp -d)
trap 'rm -rf "$tmpdir"' EXIT
trap 'rm -rf "$tmpdir"; exit 130' INT TERM

stat_value() {
  sed -n "s/^$1=//p" "$2"
}

clear_mcmini_columns() {
  r_traces="$DASH"
  r_transitions="$DASH"
  r_kinds="$DASH"
  r_counts="$DASH"
  r_exhausted="$DASH"
  r_max_depth_per_thread="$DASH"
  r_max_depth_per_trace="$DASH"
  r_transition_ceiling="$DASH"
  r_check_ms="$DASH"
}

# Runs one program once and leaves the result in the r_* variables. Never
# fails: an unrunnable program is a status=error result, not an abort.
run_program() {
  prog="$1"
  stats_file="$tmpdir/$2.stats"
  out_file="$tmpdir/$2.out"
  rm -f "$stats_file" "$out_file"

  clear_mcmini_columns
  r_elapsed_ms=0
  r_status=error

  if [ ! -x "$build_dir/$prog" ]; then
    printf 'run-bench: %s is missing or not executable in %s\n' \
      "$prog" "$build_dir" >&2
    return 0
  fi

  start_ns=$(date +%s%N)
  set +e
  timeout --kill-after=5s "${timeout_seconds}s" \
    "$build_dir/mcmini" --stats-file "$stats_file" -q \
    "$build_dir/$prog" --threads="$threads" > "$out_file" 2>&1
  rc=$?
  set -e
  end_ns=$(date +%s%N)
  r_elapsed_ms=$(( (end_ns - start_ns) / 1000000 ))

  if [ "$rc" -eq 124 ]; then
    printf 'run-bench: %s exceeded the %s second budget\n' \
      "$prog" "$timeout_seconds" >&2
    r_status=timeout
    return 0
  fi

  if [ "$rc" -ne 0 ] || [ ! -s "$stats_file" ] || ! grep -q '^traces=' "$stats_file"; then
    printf 'run-bench: %s exited %s without a usable record\n' "$prog" "$rc" >&2
    sed -n '1,5p' "$out_file" >&2
    return 0
  fi

  r_traces=$(stat_value traces "$stats_file")
  r_transitions=$(stat_value transitions "$stats_file")
  r_exhausted=$(stat_value exhausted "$stats_file")
  r_max_depth_per_thread=$(stat_value max_depth_per_thread "$stats_file")
  r_max_depth_per_trace=$(stat_value max_depth_per_trace "$stats_file")
  r_transition_ceiling=$(stat_value transition_ceiling "$stats_file")
  r_check_ms=$(stat_value check_ms "$stats_file")

  for value in "$r_traces" "$r_transitions" "$r_exhausted" \
    "$r_max_depth_per_thread" "$r_max_depth_per_trace" \
    "$r_transition_ceiling" "$r_check_ms"; do
    if [ -z "$value" ]; then
      printf 'run-bench: %s wrote an incomplete record\n' "$prog" >&2
      clear_mcmini_columns
      return 0
    fi
  done

  kinds=""
  counts=""
  for kind in $VIOLATION_KINDS; do
    tally=$(stat_value "violations_$kind" "$stats_file")
    [ -n "$tally" ] || tally=0
    if [ "$tally" -gt 0 ]; then
      kinds="${kinds:+$kinds,}$kind"
      counts="${counts:+$counts,}$kind:$tally"
    fi
  done
  r_kinds="${kinds:-$DASH}"
  r_counts="${counts:-$DASH}"

  r_status=ok
}

# Median of the numeric arguments. For an even count this is the LOWER of the
# two middle observations, not their average, so the reported number stays a
# value that was actually measured.
median() {
  printf '%s\n' "$@" | sort -n | sed -n "$(( ($# + 1) / 2 ))p"
}

row_signature() {
  printf '%s|%s|%s|%s|%s|%s|%s|%s' \
    "$r_traces" "$r_transitions" "$r_kinds" "$r_counts" "$r_exhausted" \
    "$r_max_depth_per_thread" "$r_max_depth_per_trace" "$r_transition_ceiling"
}

report_drift() {
  printf '%s\n%s\n' "$2" "$3" |
    awk -F'|' -v prog="$1" -v cols="$DETERMINISTIC_COLUMNS" '
      BEGIN { split(cols, name, " ") }
      NR == 1 { for (i = 1; i <= NF; i++) first[i] = $i; fields = NF; next }
      {
        for (i = 1; i <= fields; i++)
          if ($i != first[i])
            printf "run-bench: %s is not reproducible: %s was %s then %s\n", \
              prog, name[i], first[i], $i
      }
    ' >&2
}

# Runs one program `repeat` times and reduces the repetitions to one row.
measure_program() {
  measured="$1"
  elapsed_samples=""
  check_samples=""
  signature=""
  rep=1

  while [ "$rep" -le "$repeat" ]; do
    run_program "$measured" "$measured.$rep"
    [ "$r_status" = ok ] || return 0

    if [ "$rep" -eq 1 ]; then
      signature=$(row_signature)
    elif [ "$(row_signature)" != "$signature" ]; then
      report_drift "$measured" "$signature" "$(row_signature)"
      clear_mcmini_columns
      r_status=error
      return 0
    fi

    elapsed_samples="${elapsed_samples:+$elapsed_samples }$r_elapsed_ms"
    check_samples="${check_samples:+$check_samples }$r_check_ms"
    rep=$(( rep + 1 ))
  done

  r_elapsed_ms=$(median $elapsed_samples)
  r_check_ms=$(median $check_samples)
}

emit_row() {
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$1" "$threads" \
    "$r_traces" "$r_transitions" "$r_kinds" "$r_counts" "$r_exhausted" \
    "$r_max_depth_per_thread" "$r_max_depth_per_trace" "$r_transition_ceiling" \
    "$r_elapsed_ms" "$r_check_ms" "$r_status"
}

failures=0

run_suite() {
  header_line
  for program in $PROGRAMS; do
    measure_program "$program"
    emit_row "$program"
    [ "$r_status" = ok ] || failures=$(( failures + 1 ))
  done
}

run_command() {
  if [ -n "$out_path" ]; then
    run_suite > "$out_path"
  else
    run_suite
  fi
  [ "$failures" -eq 0 ] || exit 1
}

# --- scaling -----------------------------------------------------------------

# D-10's invariant check: a program whose transition count does not move with
# its thread flag is silently ignoring, clamping or hardcoding the count, which
# would turn a suite run at any N into a mix of scaled and frozen programs.
scaling_command() {
  frozen=0
  for program in $PROGRAMS; do
    threads=2
    measure_program "$program"
    low_status="$r_status"
    low_transitions="$r_transitions"

    threads=3
    measure_program "$program"
    high_status="$r_status"
    high_transitions="$r_transitions"

    if [ "$low_status" != ok ] || [ "$high_status" != ok ]; then
      printf '%s\tUNMEASURED\tN=2 %s, N=3 %s\n' \
        "$program" "$low_status" "$high_status"
      frozen=$(( frozen + 1 ))
    elif [ "$low_transitions" = "$high_transitions" ]; then
      printf '%s\tFROZEN\ttransitions=%s at both N=2 and N=3\n' \
        "$program" "$low_transitions"
      frozen=$(( frozen + 1 ))
    else
      printf '%s\tSCALES\ttransitions %s -> %s\n' \
        "$program" "$low_transitions" "$high_transitions"
    fi
  done

  [ "$frozen" -eq 0 ] || exit 1
}

# --- compare -----------------------------------------------------------------

header_field() {
  sed -n "s/^#[[:space:]]*$2=//p" "$1" | sed -n 1p
}

# A result file is only comparable if it carries the 13-column contract and at
# least one data row. An empty result set is a harness failure, not a
# comparison with nothing to say.
require_result_file() {
  if [ ! -r "$1" ]; then
    printf 'run-bench: cannot read result file: %s\n' "$1" >&2
    exit 1
  fi
  if [ "$(grep -v '^#' "$1" | sed -n 1p)" != "$(header_line)" ]; then
    printf 'run-bench: %s does not carry the 13-column header contract\n' "$1" >&2
    exit 1
  fi
  if [ "$(grep -v '^#' "$1" | sed 1d | grep -c . || true)" -eq 0 ]; then
    printf 'run-bench: %s contains no data rows\n' "$1" >&2
    exit 1
  fi
}

# Wall clock across Debug and Release differs by more than any optimization in
# this milestone, so an unflagged cross-build-type comparison can flatter or
# bury a real result.
warn_on_header_drift() {
  for field in commit build_type compiler cpu threads repeats; do
    base_value=$(header_field "$1" "$field")
    current_value=$(header_field "$2" "$field")
    if [ "$base_value" != "$current_value" ]; then
      printf 'WARNING: %s differs: baseline=%s current=%s\n' \
        "$field" "${base_value:-<absent>}" "${current_value:-<absent>}" >&2
    fi
  done
}

compare_command() {
  require_result_file "$compare_baseline"
  require_result_file "$compare_current"
  warn_on_header_drift "$compare_baseline" "$compare_current"

  awk -F'\t' '
    function ratio(current, base) {
      if (base + 0 <= 0) return "n/a"
      return sprintf("%.2f", (current + 0) / (base + 0))
    }
    /^#/ { next }
    $1 == "program" { next }
    NR == FNR {
      key = $1 SUBSEP $2
      order[++baseline_count] = key
      for (i = 1; i <= 13; i++) baseline[key, i] = $i
      next
    }
    {
      key = $1 SUBSEP $2
      if (!((key, 1) in baseline)) {
        extra[++extra_count] = key
        for (i = 1; i <= 13; i++) unmatched[key, i] = $i
        next
      }
      seen[key] = 1
      for (i = 1; i <= 13; i++) current[key, i] = $i
    }
    END {
      for (index_ = 1; index_ <= baseline_count; index_++) {
        key = order[index_]
        if (!(key in seen)) {
          printf "%s\tthreads=%s\tMISSING\n", baseline[key, 1], baseline[key, 2]
          continue
        }

        detail = ""
        if (baseline[key, 3] != current[key, 3]) {
          detail = detail sprintf("\ttraces=%s->%s", baseline[key, 3], current[key, 3])
          traces_changed++
        }
        if (baseline[key, 4] != current[key, 4])
          detail = detail sprintf("\ttransitions=%s->%s", baseline[key, 4], current[key, 4])
        if (baseline[key, 5] != current[key, 5]) {
          detail = detail sprintf("\tviolation_kinds=%s->%s", baseline[key, 5], current[key, 5])
          kinds_changed++
        }

        truncation = ""
        if (baseline[key, 7] == "no" || current[key, 7] == "no") {
          truncation = "\tTRUNCATED"
          truncated++
        }

        printf "%s\tthreads=%s\t%s%s\telapsed=%s\tcheck=%s%s\n",
          baseline[key, 1], baseline[key, 2],
          (detail == "" ? "MATCH" : "CHANGED"), detail,
          ratio(current[key, 11], baseline[key, 11]),
          ratio(current[key, 12], baseline[key, 12]),
          truncation
      }

      for (index_ = 1; index_ <= extra_count; index_++) {
        key = extra[index_]
        printf "%s\tthreads=%s\tEXTRA\n", unmatched[key, 1], unmatched[key, 2]
      }

      printf "SUMMARY\tprograms=%d\tkinds_changed=%d\ttraces_changed=%d\ttruncated=%d\n",
        baseline_count + extra_count, kinds_changed + 0, traces_changed + 0,
        truncated + 0
    }
  ' "$compare_baseline" "$compare_current"
}

case "$subcommand" in
  compare) compare_command ;;
  scaling) scaling_command ;;
  *) run_command ;;
esac
