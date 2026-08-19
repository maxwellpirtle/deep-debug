// Bounded-buffer producer/consumer with the semaphores paired correctly: the
// producer waits on `empty` and posts `full`, the consumer waits on `full` and
// posts `empty`. Each of the N-1 producers produces exactly one item and the
// single consumer consumes exactly N-1 items, so the program terminates for
// every accepted N with no deadlock and no orphaned waiter.
//
// The `empty` and `full` operations are on DISTINCT semaphores throughout.
// That independence is what a sharper dependence relation gets to exploit.

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
    sem_wait(&full);
    pthread_mutex_lock(&mutex);
    out = (out + 1) % BUFFER_SIZE;
    pthread_mutex_unlock(&mutex);
    sem_post(&empty);
  }
  return NULL;
}

int main(int argc, char *argv[]) {
  static const char usage[] =
      "Usage: sem-clean [--threads=N] [--help]\n"
      "  N-1 producers and 1 consumer over a one-slot buffer with correctly\n"
      "  paired semaphores. Terminates for every accepted N (2 through 19).\n"
      "  Default N is 3.\n";
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
