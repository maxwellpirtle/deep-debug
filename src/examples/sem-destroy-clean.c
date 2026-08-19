// The positive control for `sem_destroy` translation: a program that destroys
// a semaphore, and does so legally. The main thread initialises the semaphore,
// creates one worker that waits then posts, JOINS that worker, and only then
// destroys the semaphore. Nothing touches it after the destroy, so no trace
// reaches the use-after-destroy path and every violation counter must be zero.
//
// Before `sem_destroy_callback` returned a transition, this program did not
// merely report the wrong thing -- it killed McMini with an `execution_error`
// naming an unregistered mailbox type, because the callback returned NULL.
//
// DELIBERATE DEVIATION from the project convention that a target program takes
// its thread count from the command line. This program is the paired control
// for `sem-destroy-uaf`, whose whole point is an assertion about a FIXED
// ordering (see that file); a thread count that varied at the command line
// would vary the interleaving set the assertion is made over, turning a
// regression test with one right answer into one whose right answer depends on
// an argument. The two programs are held to the same shape so they differ in
// exactly one respect: where the destroy sits. Two threads total, inside the
// project's three-interacting-thread ceiling. Neither program joins the frozen
// benchmark suite or any measurement path.

#include <pthread.h>
#include <semaphore.h>
#include <stddef.h>

static sem_t sem;

static void *worker_doit(void *unused) {
  (void)unused;
  sem_wait(&sem);
  sem_post(&sem);
  return NULL;
}

int main(void) {
  pthread_t worker;

  sem_init(&sem, 0, 1);
  pthread_create(&worker, NULL, &worker_doit, NULL);
  pthread_join(worker, NULL);
  sem_destroy(&sem);
  return 0;
}
