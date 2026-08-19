#!/bin/sh
#
# Run the McMini benchmark suite and emit one tab-separated row per program.
#
#   sh script/run-bench.sh [--build-dir DIR] [--threads N] [--help]
#
# Only the TSV result set reaches stdout. McMini writes a trace dump on every
# violating trace, so each invocation's output is redirected into a temporary
# directory: an unredirected run would interleave trace dumps into the result
# set and load the wall-clock number with trace-dump I/O.

set -eu

build_dir="${BENCH_BUILD_DIR:-build}"
threads="${BENCH_THREADS:-3}"

PROGRAMS="mutex-bug"

usage() {
  cat <<'EOF'
Usage: run-bench.sh [--build-dir DIR] [--threads N] [--help]

  --build-dir DIR  Directory holding mcmini, libmcmini.so and every benchmark
                   binary (default: build; also read from BENCH_BUILD_DIR).
  --threads N      Thread count passed to each benchmark program
                   (default: 3; also read from BENCH_THREADS).
EOF
}

require_value() {
  if [ "$2" -lt 2 ]; then
    printf 'run-bench: %s requires a value\n' "$1" >&2
    exit 1
  fi
}

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
    --help | -h)
      usage
      exit 0
      ;;
    *)
      printf 'run-bench: unrecognized option: %s\n' "$1" >&2
      usage >&2
      exit 1
      ;;
  esac
done

tmpdir=$(mktemp -d)
trap 'rm -rf "$tmpdir"' EXIT INT TERM

stat_value() {
  sed -n "s/^$1=//p" "$2"
}

printf 'program\tthreads\ttraces\ttransitions\tstatus\n'

for prog in $PROGRAMS; do
  "$build_dir/mcmini" --stats-file "$tmpdir/$prog.stats" -q \
    "$build_dir/$prog" --threads="$threads" > "$tmpdir/$prog.out" 2>&1
  printf '%s\t%s\t%s\t%s\t%s\n' \
    "$prog" "$threads" \
    "$(stat_value traces "$tmpdir/$prog.stats")" \
    "$(stat_value transitions "$tmpdir/$prog.stats")" \
    "ok"
done
