// The negative control: a use-after-destroy that must be reported as
// undefined behaviour and NOT as a deadlock. The main thread initialises the
// semaphore, destroys it, and only THEN creates the worker that waits on it.
//
// The destroy strictly precedes the thread creation in the main thread's own
// program order, so the worker's wait follows the destroy in every
// interleaving. That is what makes `violations_undefined_behavior >= 1` a
// deterministic expectation rather than a probabilistic one.
//
// `violations_deadlock=0` is the load-bearing half of the expectation. Had
// use-after-destroy been detected by returning `status::undefined` from
// `sem_wait::modify` instead of from the translation callback, `apply_to`
// would have collapsed it into `disabled`, dropping the runner out of
// `get_enabled_runners()` -- and this program would report a DEADLOCK, a
// semantically wrong violation kind that reads as a right one.
//
// DELIBERATE DEVIATION from the project convention that a target program takes
// its thread count from the command line: this program is an assertion about a
// fixed ordering, and a thread count that varied at the command line would
// vary the interleaving set that assertion is made over. Two threads total,
// inside the project's three-interacting-thread ceiling. It joins neither the
// frozen benchmark suite nor any measurement path.

#include <pthread.h>
#include <semaphore.h>
#include <stddef.h>

static sem_t sem;

static void *worker_doit(void *unused) {
  (void)unused;
  sem_wait(&sem);
  return NULL;
}

int main(void) {
  pthread_t worker;

  sem_init(&sem, 0, 1);
  sem_destroy(&sem);
  pthread_create(&worker, NULL, &worker_doit, NULL);
  pthread_join(worker, NULL);
  return 0;
}
