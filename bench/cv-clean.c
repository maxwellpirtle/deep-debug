// The correct counterpart to `cv-bug.c`: each of the N-1 waiters re-tests the
// predicate in a `while` loop around `pthread_cond_wait`, and the single
// signaler sets `ready` under the mutex and calls `pthread_cond_broadcast`.
//
// Every waiter observes the predicate whether it arrives before or after the
// broadcast, so the program terminates for every accepted N. The two files are
// structurally parallel: the pair isolates the predicate loop and the
// broadcast, and nothing else.

#include <pthread.h>
#include <stddef.h>

#include "bench_args.h"

static pthread_mutex_t mutex;
static pthread_cond_t cond;
static int ready;

static void *waiter_doit(void *unused) {
  (void)unused;
  pthread_mutex_lock(&mutex);
  while (!ready) {
    pthread_cond_wait(&cond, &mutex);
  }
  pthread_mutex_unlock(&mutex);
  return NULL;
}

static void *signaler_doit(void *unused) {
  (void)unused;
  pthread_mutex_lock(&mutex);
  ready = 1;
  pthread_cond_broadcast(&cond);
  pthread_mutex_unlock(&mutex);
  return NULL;
}

int main(int argc, char *argv[]) {
  static const char usage[] =
      "Usage: cv-clean [--threads=N] [--help]\n"
      "  N-1 waiters and 1 signaler. The waiters re-test the predicate in a\n"
      "  loop and the signaler broadcasts, so the program terminates for\n"
      "  every accepted N (2 through 19). Default N is 3.\n";
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
