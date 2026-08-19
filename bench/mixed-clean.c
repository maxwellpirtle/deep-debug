// The same three primitives and the same worker/coordinator split as
// `mixed-bug.c`, with one correction: every thread acquires the semaphore
// before the mutex, so there is a single consistent global acquisition order
// and no cycle can form.
//
// The termination handshake is unchanged -- a predicate re-tested in a `while`
// loop with `pthread_cond_broadcast` -- and no thread holds the semaphore
// token across a condition wait, so the program terminates for every accepted
// N.

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
  sem_wait(&sem);
  pthread_mutex_lock(&mutex);
  work_done++;
  pthread_mutex_unlock(&mutex);
  sem_post(&sem);

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
      "Usage: mixed-clean [--threads=N] [--help]\n"
      "  N-1 workers and 1 coordinator over a mutex, a semaphore and a\n"
      "  condition variable, all acquired in one consistent order.\n"
      "  Terminates for every accepted N (2 through 19). Default N is 3.\n";
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
