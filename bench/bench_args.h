// Shared command-line parsing for the McMini benchmark programs.

#pragma once

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// A benchmark needs two interacting threads for any interleaving to exist, and
// MAX_TOTAL_THREADS_IN_PROGRAM is 20 counting the main thread.
#define BENCH_MIN_THREADS 2
#define BENCH_MAX_THREADS 19

static inline void bench_illegal_threads_value(void) {
  fprintf(stderr, "bench: --threads: illegal value\n");
  exit(1);
}

/**
 * Return the number of interacting threads requested on the command line.
 *
 * Recognizes `--threads=N` and `--help`; the default is 3. A value that is not
 * a whole number, or that falls outside [BENCH_MIN_THREADS,
 * BENCH_MAX_THREADS], terminates the program. Nothing is clamped and nothing
 * is ignored: a benchmark that silently ran at a thread count other than the
 * one requested would report a measurement comparable to nothing.
 */
static inline int bench_threads_from_args(int argc, char **argv,
                                          const char *usage) {
  static const char prefix[] = "--threads=";
  const size_t prefix_len = sizeof(prefix) - 1;
  int threads = 3;
  int i;

  for (i = 1; i < argc; i++) {
    const char *value;
    char *endptr;
    long parsed;

    if (strcmp(argv[i], "--help") == 0) {
      printf("%s", usage);
      exit(0);
    }
    if (strncmp(argv[i], prefix, prefix_len) != 0) {
      fprintf(stderr, "bench: unrecognized option: %s\n%s", argv[i], usage);
      exit(1);
    }

    value = argv[i] + prefix_len;
    if (value[0] == '\0') bench_illegal_threads_value();

    errno = 0;
    parsed = strtol(value, &endptr, 10);
    if (errno != 0 || endptr[0] != '\0' || parsed < 0) {
      bench_illegal_threads_value();
    }
    if (parsed < BENCH_MIN_THREADS || parsed > BENCH_MAX_THREADS) {
      fprintf(stderr, "bench: --threads must be between %d and %d\n",
              BENCH_MIN_THREADS, BENCH_MAX_THREADS);
      exit(1);
    }
    threads = (int)parsed;
  }
  return threads;
}
