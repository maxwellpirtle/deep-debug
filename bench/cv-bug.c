// The textbook lost wakeup: each of the N-1 waiters takes the mutex and calls
// `pthread_cond_wait` without testing the predicate and without a surrounding
// loop, while the single signaler sets `ready` and calls
// `pthread_cond_signal` exactly once.
//
// Two failure modes, both reachable at N = 2: the signal is delivered before a
// waiter reaches its wait, and more than one waiter is outstanding when the
// single signal arrives. The split is N-1 waiters and 1 signaler.

#include <pthread.h>
#include <stddef.h>

#include "bench_args.h"

static pthread_mutex_t mutex;
static pthread_cond_t cond;
static int ready;

static void *waiter_doit(void *unused) {
  (void)unused;
  pthread_mutex_lock(&mutex);
  pthread_cond_wait(&cond, &mutex);
  pthread_mutex_unlock(&mutex);
  return NULL;
}

static void *signaler_doit(void *unused) {
  (void)unused;
  pthread_mutex_lock(&mutex);
  ready = 1;
  pthread_cond_signal(&cond);
  pthread_mutex_unlock(&mutex);
  return NULL;
}

int main(int argc, char *argv[]) {
  static const char usage[] =
      "Usage: cv-bug [--threads=N] [--help]\n"
      "  N-1 waiters and 1 signaler. The waiters never test the predicate and\n"
      "  never loop, so a lost wakeup is reachable at every accepted N\n"
      "  (2 through 19). Default N is 3.\n";
  const int num_threads = bench_threads_from_args(argc, argv, usage);

  pthread_t thread[num_threads];
  const int num_waiters = num_threads - 1;
  int i;

  pthread_mutex_init(&mutex, NULL);
  pthread_cond_init(&cond, NULL);

  for (i = 0; i < num_waiters; i++) {
    pthread_create(&thread[i], NULL, &waiter_doit, NULL);
  }
  pthread_create(&thread[num_waiters], NULL, &signaler_doit, NULL);

  for (i = 0; i < num_threads; i++) {
    pthread_join(thread[i], NULL);
  }
  return 0;
}
