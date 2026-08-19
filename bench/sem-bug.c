// Bounded-buffer producer/consumer differing from `sem-clean.c` by exactly one
// line: the consumer takes the mutex BEFORE waiting on `full` instead of
// after. Blocking on a semaphore while holding a mutex creates a hold-and-wait
// cycle -- a consumer that reaches its wait before any producer has posted
// `full` blocks holding the mutex the producers need, and the producers block
// on that mutex, so nobody can ever post `full`.
//
// The cycle needs one producer and one consumer, so it is reachable at every
// accepted N (2 through 19). It is interleaving-sensitive: the run in which a
// producer completes first terminates normally, which is precisely why finding
// it is the model checker's job. The split is N-1 producers and 1 consumer.

#include <pthread.h>
#include <semaphore.h>
#include <stddef.h>

#include "bench_args.h"

// One slot keeps the state space small enough to explore routinely.
#define BUFFER_SIZE 1

static sem_t empty;
static sem_t full;
static pthread_mutex_t mutex;
static int buffer[BUFFER_SIZE];
static int in;
static int out;
static int num_producers;

static void *producer_doit(void *unused) {
  (void)unused;
  sem_wait(&empty);
  pthread_mutex_lock(&mutex);
  buffer[in] = 1;
  in = (in + 1) % BUFFER_SIZE;
  pthread_mutex_unlock(&mutex);
  sem_post(&full);
  return NULL;
}

static void *consumer_doit(void *unused) {
  int i;
  (void)unused;
  for (i = 0; i < num_producers; i++) {
    pthread_mutex_lock(&mutex);
    sem_wait(&full);
    out = (out + 1) % BUFFER_SIZE;
    pthread_mutex_unlock(&mutex);
    sem_post(&empty);
  }
  return NULL;
}

int main(int argc, char *argv[]) {
  static const char usage[] =
      "Usage: sem-bug [--threads=N] [--help]\n"
      "  N-1 producers and 1 consumer over a one-slot buffer. The consumer\n"
      "  waits on `full` while holding the mutex, so a hold-and-wait deadlock\n"
      "  is reachable at every accepted N (2 through 19). Default N is 3.\n";
  const int num_threads = bench_threads_from_args(argc, argv, usage);

  pthread_t thread[num_threads];
  int i;

  num_producers = num_threads - 1;

  pthread_mutex_init(&mutex, NULL);
  sem_init(&empty, 0, BUFFER_SIZE);
  sem_init(&full, 0, 0);

  for (i = 0; i < num_producers; i++) {
    pthread_create(&thread[i], NULL, &producer_doit, NULL);
  }
  pthread_create(&thread[num_producers], NULL, &consumer_doit, NULL);

  for (i = 0; i < num_threads; i++) {
    pthread_join(thread[i], NULL);
  }
  return 0;
}
