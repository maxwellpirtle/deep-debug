// The positive control for static-initializer recognition on condition
// variables (CTRL-03, INIT-02): four DISTINCT file-scope static
// pthread_cond_t variables, each statically initialized with the standard
// initializer macro and each reached FIRST by exactly one of the four
// operations -- signal, broadcast, destroy, and wait. One variable cannot be
// first-operated four times inside a single run, so four variables carry the
// four first-operation cases. The wait path also uses one file-scope static
// mutex, statically initialized the same way. Nothing in this program is ever
// explicitly initialized (no init call of any kind anywhere in this program).
//
// Program shape: main signals cv_a (no waiter -- a legal lost signal), then
// broadcasts cv_b (no waiter), then destroys cv_c (destroy as the variable's
// first operation is legal), then locks the mutex, spawns one helper thread,
// and waits on cv_d in a predicate loop; the helper locks the mutex, sets the
// predicate, signals cv_d, and unlocks; main joins. Because main holds the
// mutex from before pthread_create until it is parked inside the wait, cv_d's
// first operation is the wait-side enqueue on EVERY interleaving -- and the
// enqueue site also exercises the second (mutex) flag byte with a static
// mutex that main already observed at its own lock, which must stay clean
// (D-11 from-main safety).
//
// Expected verdict: clean. The stats file shows every violations_* counter
// equal to 0 and exhausted=yes, and McMini prints "Model checking
// completed!". The verdict lives in the stats data and the stdout marker
// only -- McMini's process exit code is 0 for clean AND for violation runs.
//
// Why each first operation is legal: a static initializer is legal
// initialization, and glibc's statically-initialized condition variable stays
// byte-equal to the all-zero initializer pattern even after a signal or
// broadcast with no waiters (verified on this machine), so EVERY later first
// observation still carries the static-init flag set -- including destroy as
// the variable's very first operation. The wrapper memcmps each cv in-process
// and writes the flag into the mailbox payload; the model-side callbacks see
// an unobserved cv with the flag set and lazily register it as initialized
// instead of throwing.
//
// Regression guarded: any spurious "Attempting to signal/broadcast on/
// destroy/wait on an uninitialized condition variable" report here means the
// flag path broke between the wrapper predicate, the payload offset, and the
// callback decision; a spurious uninitialized-mutex report at the wait means
// the D-11 second flag byte or the contains() guard broke.
//
// DELIBERATE DEVIATION from the project convention that a target program
// takes its thread count from the command line. This program is the paired
// control for `cond-garbage-ub`; the pair is held to the same fixed shape so
// the two differ in exactly one respect: whether the cv bytes match the
// static initializer. A thread count that varied at the command line would
// vary the interleaving set the clean verdict is asserted over. Two threads
// total (main + 1 helper), inside the project's three-interacting-thread
// ceiling. Neither program joins the frozen benchmark suite or any
// measurement path.

#include <pthread.h>
#include <stddef.h>

static pthread_cond_t cv_a = PTHREAD_COND_INITIALIZER;  /* first op: signal */
static pthread_cond_t cv_b = PTHREAD_COND_INITIALIZER;  /* first op: broadcast */
static pthread_cond_t cv_c = PTHREAD_COND_INITIALIZER;  /* first op: destroy */
static pthread_cond_t cv_d = PTHREAD_COND_INITIALIZER;  /* first op: wait */
static pthread_mutex_t mut = PTHREAD_MUTEX_INITIALIZER;
static int predicate = 0;

static void *helper_doit(void *unused) {
  (void)unused;
  pthread_mutex_lock(&mut);
  predicate = 1;
  pthread_cond_signal(&cv_d);
  pthread_mutex_unlock(&mut);
  return NULL;
}

int main(void) {
  pthread_t helper;

  pthread_cond_signal(&cv_a);     /* legal lost signal: no waiter */
  pthread_cond_broadcast(&cv_b);  /* legal lost broadcast: no waiter */
  pthread_cond_destroy(&cv_c);    /* legal destroy-as-first-operation */

  pthread_mutex_lock(&mut);
  pthread_create(&helper, NULL, &helper_doit, NULL);
  while (!predicate) pthread_cond_wait(&cv_d, &mut);
  pthread_mutex_unlock(&mut);
  pthread_join(helper, NULL);
  return 0;
}
