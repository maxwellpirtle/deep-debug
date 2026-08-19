// The `mutex-bug` philosopher ring with its cycle broken: philosopher `N - 1`
// takes its right fork before its left, while every other philosopher takes
// left before right. That single inversion removes the circular wait for every
// N >= 2, so the program always terminates.
//
// Everything else is identical to `mutex-bug.c` so the pair isolates exactly
// one difference.

#include <pthread.h>
#include <stddef.h>

#include "bench_args.h"

struct forks {
  pthread_mutex_t *first_fork;
  pthread_mutex_t *second_fork;
};

static void *philosopher_doit(void *forks_arg) {
  struct forks *forks = forks_arg;
  pthread_mutex_lock(forks->first_fork);
  pthread_mutex_lock(forks->second_fork);
  pthread_mutex_unlock(forks->first_fork);
  pthread_mutex_unlock(forks->second_fork);
  return NULL;
}

int main(int argc, char *argv[]) {
  static const char usage[] =
      "Usage: mutex-clean [--threads=N] [--help]\n"
      "  N philosophers on a mutex ring with philosopher N-1's acquisition\n"
      "  order inverted. Terminates for every accepted N (2 through 19).\n"
      "  Default N is 3.\n";
  const int num_threads = bench_threads_from_args(argc, argv, usage);

  pthread_t thread[num_threads];
  pthread_mutex_t mutex_resource[num_threads];
  struct forks forks[num_threads];
  int i;

  for (i = 0; i < num_threads; i++) {
    pthread_mutex_init(&mutex_resource[i], NULL);
  }
  for (i = 0; i < num_threads; i++) {
    pthread_mutex_t *left = &mutex_resource[i];
    pthread_mutex_t *right = &mutex_resource[(i + 1) % num_threads];
    if (i == num_threads - 1) {
      forks[i] = (struct forks){right, left};
    } else {
      forks[i] = (struct forks){left, right};
    }
  }
  for (i = 0; i < num_threads; i++) {
    pthread_create(&thread[i], NULL, &philosopher_doit, &forks[i]);
  }
  for (i = 0; i < num_threads; i++) {
    pthread_join(thread[i], NULL);
  }
  return 0;
}
