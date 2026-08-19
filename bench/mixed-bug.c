// All three primitive families in one program, with a lock-order inversion
// ACROSS primitive types rather than across two mutexes: the N-1 workers take
// the mutex and then wait on the semaphore, while the coordinator waits on the
// semaphore and then takes the mutex.
//
// A worker holding the mutex and blocked on the semaphore, and the coordinator
// holding the semaphore token and blocked on the mutex, is a cycle spanning a
// mutex and a semaphore. It needs one worker and one coordinator, so it is
// reachable at every accepted N (2 through 19), and it is interleaving-
// sensitive: the run in which either side completes its pair first terminates.
//
// The condition variable carries the termination handshake and is identical to
// the one in `mixed-clean.c`; the acquisition order is the only difference
// between the pair.

#include <pthread.h>
#include <semaphore.h>
#include <stddef.h>

#include "bench_args.h"

static pthread_mutex_t mutex;
static pthread_cond_t cond;
static sem_t sem;
static int work_done;
static int finished;

static void *worker_doit(void *unused) {
  (void)unused;
  pthread_mutex_lock(&mutex);
  sem_wait(&sem);
  work_done++;
  sem_post(&sem);
  pthread_mutex_unlock(&mutex);

  pthread_mutex_lock(&mutex);
  while (!finished) {
    pthread_cond_wait(&cond, &mutex);
  }
  pthread_mutex_unlock(&mutex);
  return NULL;
}

static void *coordinator_doit(void *unused) {
  (void)unused;
  sem_wait(&sem);
  pthread_mutex_lock(&mutex);
  finished = 1;
  pthread_cond_broadcast(&cond);
  pthread_mutex_unlock(&mutex);
  sem_post(&sem);
  return NULL;
}

int main(int argc, char *argv[]) {
  static const char usage[] =
      "Usage: mixed-bug [--threads=N] [--help]\n"
      "  N-1 workers and 1 coordinator over a mutex, a semaphore and a\n"
      "  condition variable. The workers take the mutex before the semaphore\n"
      "  and the coordinator takes them in the opposite order, so a cross-\n"
      "  primitive deadlock is reachable at every accepted N (2 through 19).\n"
      "  Default N is 3.\n";
  const int num_threads = bench_threads_from_args(argc, argv, usage);

  pthread_t thread[num_threads];
  const int num_workers = num_threads - 1;
  int i;

  pthread_mutex_init(&mutex, NULL);
  pthread_cond_init(&cond, NULL);
  sem_init(&sem, 0, 1);

  for (i = 0; i < num_workers; i++) {
    pthread_create(&thread[i], NULL, &worker_doit, NULL);
  }
  pthread_create(&thread[num_workers], NULL, &coordinator_doit, NULL);

  for (i = 0; i < num_threads; i++) {
    pthread_join(thread[i], NULL);
  }
  return 0;
}
