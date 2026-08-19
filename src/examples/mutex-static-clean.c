// The positive control for static-initializer recognition on mutexes
// (CTRL-01): a multi-threaded program whose only mutex is declared with
// PTHREAD_MUTEX_INITIALIZER and never explicitly initialized (no init call
// anywhere in this program). Two workers each lock the mutex, increment a
// shared counter, and unlock; main joins both.
//
// Expected verdict: clean. The stats file shows all four violations_*
// counters equal to 0 and exhausted=yes, and McMini prints
// "Model checking completed!". The verdict lives in the stats data and the
// stdout marker only -- McMini's process exit code is 0 for clean AND for
// violation runs, so exit codes prove nothing here.
//
// Why this is clean: a static initializer is legal initialization. The
// wrapper in libmcmini.so memcmps the mutex against the
// PTHREAD_MUTEX_INITIALIZER byte pattern in-process and writes the
// static-init flag into the mailbox payload; the model-side callback sees an
// unobserved mutex with the flag set and lazily registers it as initialized
// (mutex::unlocked) instead of throwing.
//
// Regression guarded: a spurious "Attempting to lock an uninitialized mutex"
// (or unlock) report here means the flag path broke somewhere between the
// wrapper predicate, the mailbox payload offset, and the callback decision.
//
// DELIBERATE DEVIATION from the project convention that a target program
// takes its thread count from the command line. This program is the paired
// control for `mutex-garbage-ub`; the pair is held to the same fixed shape so
// the two differ in exactly one respect: whether the mutex bytes match the
// static initializer. A thread count that varied at the command line would
// vary the interleaving set the clean verdict is asserted over, turning a
// regression test with one right answer into one whose right answer depends
// on an argument. Three threads total (main + 2 workers), inside the
// project's three-interacting-thread ceiling. Neither program joins the
// frozen benchmark suite or any measurement path.

#include <pthread.h>
#include <stddef.h>

static pthread_mutex_t mut = PTHREAD_MUTEX_INITIALIZER;
static int counter = 0;

static void *worker_doit(void *unused) {
  (void)unused;
  pthread_mutex_lock(&mut);
  counter++;
  pthread_mutex_unlock(&mut);
  return NULL;
}

int main(void) {
  pthread_t w1, w2;

  pthread_create(&w1, NULL, &worker_doit, NULL);
  pthread_create(&w2, NULL, &worker_doit, NULL);
  pthread_join(w1, NULL);
  pthread_join(w2, NULL);
  return 0;
}
