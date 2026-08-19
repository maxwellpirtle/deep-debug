// The negative control for static-initializer recognition on condition
// variables (CTRL-04): a single-threaded program that performs exactly one
// operation on a stack-local pthread_cond_t whose every byte has been
// deterministically set to 0xFF. The operation under test is selected by
// argv[1]: "wait" (the default when no argument is given), "signal",
// "broadcast", or "destroy". Any other selector prints usage to stderr and
// returns 1 before any condition-variable operation. The wait selector first
// locks a file-scope static mutex -- the lock observes the mutex in the
// model, so the only uninitialized primitive at the wait is the cv itself.
//
// Expected verdict, every selector: stdout contains "UNDEFINED BEHAVIOR:"
// followed by a message naming an uninitialized condition variable and THAT
// operation ("Attempting to wait on an uninitialized condition variable" for
// wait -- the shared wording of the enqueue/wait pair, "Attempting to signal
// an uninitialized condition variable" for signal, "Attempting to broadcast
// on an uninitialized condition variable" for broadcast, "Attempting to
// destroy an uninitialized condition variable" for destroy); the stats file
// shows violations_undefined_behavior=1 and exhausted=no. The McMini process
// exit code is still 0 -- verdicts are stats data and stdout markers, never
// exit codes.
//
// Why this is UB: 0xFF across the full sizeof cannot memcmp-equal the
// all-zero static-initializer pattern, so the wrapper writes the flag as
// not-static-init; the model-side callback sees an unobserved cv with the
// flag clear and throws in the coordinator WHILE THE TARGET IS PARKED.
// Before this phase these garbage cond operations did not merely report the
// wrong thing -- the silent registration resumed the target into glibc,
// which spins forever on the 0xFF bytes, and McMini HUNG. The restored throw
// fires before the target ever resumes, so the verdict is prompt and named.
// The memset is deliberate: a genuinely uninitialized local would have
// indeterminate bytes and a nondeterministic verdict; 0xFF is unambiguously
// distinct from the initializer on every run.
//
// DELIBERATE DEVIATION from the project convention that a target program
// takes its thread count from the command line, and from the one-behavior
// rule via the argv[1] operation selector: the first undefined-behavior
// report stops the run immediately, so a single invocation can demonstrate
// exactly one operation -- testing four operations requires either four
// programs held identical but for one line, or one program with a selector.
// The selector keeps the pair-discipline of cond-static-clean (fixed shape,
// one respect of difference) while letting each invocation assert one
// operation-named message. Single-threaded: the UB fires on the first cond
// operation of the first thread, so interleaving is irrelevant. This program
// joins neither the frozen benchmark suite nor any measurement path.

#include <pthread.h>
#include <stdio.h>
#include <string.h>

static pthread_mutex_t mut = PTHREAD_MUTEX_INITIALIZER;

int main(int argc, char *argv[]) {
  pthread_cond_t garbage;
  memset(&garbage, 0xFF, sizeof(garbage));

  if (argc < 2 || strcmp(argv[1], "wait") == 0) {
    pthread_mutex_lock(&mut); /* observes the mutex; the cv stays garbage */
    pthread_cond_wait(&garbage, &mut);
    pthread_mutex_unlock(&mut);
  } else if (strcmp(argv[1], "signal") == 0) {
    pthread_cond_signal(&garbage);
  } else if (strcmp(argv[1], "broadcast") == 0) {
    pthread_cond_broadcast(&garbage);
  } else if (strcmp(argv[1], "destroy") == 0) {
    pthread_cond_destroy(&garbage);
  } else {
    fprintf(stderr, "usage: %s [wait|signal|broadcast|destroy]\n", argv[0]);
    return 1;
  }
  return 0;
}
