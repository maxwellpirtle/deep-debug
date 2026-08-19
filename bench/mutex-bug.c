// N philosophers arranged in a mutex cycle: philosopher `i` takes fork `i`
// then fork `(i + 1) % N`, which deadlocks for every N >= 2.
//
// The program is silent and contains no delay calls: it is a wall-clock
// instrument, and anything it does outside the synchronization operations
// under test distorts the number being measured.

#include <pthread.h>
#include <stddef.h>

#include "bench_args.h"

struct forks {
  pthread_mutex_t *left_fork;
  pthread_mutex_t *right_fork;
};

static void *philosopher_doit(void *forks_arg) {
  struct forks *forks = forks_arg;
  pthread_mutex_lock(forks->left_fork);
  pthread_mutex_lock(forks->right_fork);
  pthread_mutex_unlock(forks->left_fork);
  pthread_mutex_unlock(forks->right_fork);
  return NULL;
}

int main(int argc, char *argv[]) {
  static const char usage[] =
      "Usage: mutex-bug [--threads=N] [--help]\n"
      "  N philosophers arranged in a mutex cycle. Deadlocks for every\n"
      "  accepted N (2 through 19). Default N is 3.\n";
  const int num_threads = bench_threads_from_args(argc, argv, usage);

  pthread_t thread[num_threads];
  pthread_mutex_t mutex_resource[num_threads];
  struct forks forks[num_threads];
  int i;

  for (i = 0; i < num_threads; i++) {
    pthread_mutex_init(&mutex_resource[i], NULL);
    forks[i] = (struct forks){&mutex_resource[i],
                              &mutex_resource[(i + 1) % num_threads]};
  }
  for (i = 0; i < num_threads; i++) {
    pthread_create(&thread[i], NULL, &philosopher_doit, &forks[i]);
  }
  for (i = 0; i < num_threads; i++) {
    pthread_join(thread[i], NULL);
  }
  return 0;
}
