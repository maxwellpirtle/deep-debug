// The negative control for static-initializer recognition on mutexes
// (CTRL-02): a single-threaded program that performs exactly one operation on
// a stack-local pthread_mutex_t whose every byte has been deterministically
// set to 0xFF. The operation under test is selected by argv[1]: "lock"
// (the default when no argument is given) locks the garbage mutex; "unlock"
// unlocks it. Any other selector prints usage to stderr and returns 1 before
// any mutex operation.
//
// Expected verdict, either selector: stdout contains "UNDEFINED BEHAVIOR:"
// followed by a message naming THAT operation ("Attempting to lock an
// uninitialized mutex" for lock, "Attempting to unlock an uninitialized
// mutex" for unlock); the stats file shows violations_undefined_behavior=1
// and exhausted=no. The McMini process exit code is still 0 -- verdicts are
// stats data and stdout markers, never exit codes.
//
// Why this is UB: 0xFF across the full sizeof cannot memcmp-equal the
// all-zero PTHREAD_MUTEX_INITIALIZER pattern, so the wrapper writes the
// flag as not-static-init; the model-side callback sees an unobserved mutex
// with the flag clear and throws in the coordinator before the target ever
// resumes into glibc (which could otherwise spin forever on the garbage
// bytes). The memset is deliberate: a genuinely uninitialized local would
// have indeterminate bytes and a nondeterministic verdict; 0xFF is
// unambiguously distinct from the initializer on every run.
//
// DELIBERATE DEVIATION from the project convention that a target program
// takes its thread count from the command line, and from the one-behavior
// rule via the argv[1] operation selector: the first undefined-behavior
// report stops the run immediately, so a single invocation can demonstrate
// exactly one operation -- testing both lock and unlock requires either two
// programs held identical but for one line, or one program with a selector.
// The selector keeps the pair-discipline of mutex-static-clean (fixed shape,
// one respect of difference) while letting each invocation assert one
// operation-named message. Single-threaded: the UB fires on the first
// operation of the first thread, so interleaving is irrelevant.
//
// Note: pthread_mutex_destroy is NOT intercepted by libmcmini.so (no wrapper,
// no translation callback), so destroy-on-garbage is invisible to McMini and
// cannot be a tested operation here. This program joins neither the frozen
// benchmark suite nor any measurement path.

#include <pthread.h>
#include <stdio.h>
#include <string.h>

int main(int argc, char *argv[]) {
  pthread_mutex_t garbage;
  memset(&garbage, 0xFF, sizeof(garbage));

  if (argc < 2 || strcmp(argv[1], "lock") == 0) {
    pthread_mutex_lock(&garbage);
  } else if (strcmp(argv[1], "unlock") == 0) {
    pthread_mutex_unlock(&garbage);
  } else {
    fprintf(stderr, "usage: %s [lock|unlock]\n", argv[0]);
    return 1;
  }
  return 0;
}
