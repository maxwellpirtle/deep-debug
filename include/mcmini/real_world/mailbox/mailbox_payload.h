#pragma once

#ifdef __cplusplus
extern "C" {
#endif

#include <pthread.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include "mcmini/mem.h"

/**
 * The mailbox payload contract for static-initializer flags.
 *
 * The wrapper (`libmcmini.so`, C11) and the model callbacks (C++11) both
 * compile against this header, and it is the ONLY place a flag offset is
 * derived. Layout rule (D-01): one flag byte per pointer in the payload,
 * with the whole flag block appended after the whole pointer block, in
 * pointer order. Concretely, inside the untouched `runner_mailbox.cnts`:
 *
 *   - one-pointer operations (mutex lock/unlock, cond
 *     signal/broadcast/destroy): `[ptr:8][flag:1]` -- the flag lives at
 *     `mcmini_payload_flag_offset(1, 0)`;
 *   - two-pointer operations (cond enqueue, cond wait):
 *     `[cond*:8][mut*:8][cond_flag:1][mut_flag:1]` -- the cond flag lives
 *     at `mcmini_payload_flag_offset(2, 0)`, the mutex flag at
 *     `mcmini_payload_flag_offset(2, 1)`.
 *
 * A writer always stores exactly one of the two named constants below at
 * every write site (D-03): there is no third "unknown" value, and the model
 * never reads a byte the wrapper did not write for the current transition.
 */

/** The primitive's bytes equal its glibc PTHREAD_*_INITIALIZER pattern. */
#define MCMINI_PRIMITIVE_STATIC_INIT ((uint8_t)1)
/** The primitive's bytes differ from the static-initializer pattern. */
#define MCMINI_PRIMITIVE_NOT_STATIC_INIT ((uint8_t)0)

/**
 * Report whether `m` is byte-equal to PTHREAD_MUTEX_INITIALIZER.
 *
 * Equality is full-`sizeof` byte equality against a prototype with static
 * storage duration (D-05): every byte of the prototype, padding included,
 * is zero-initialized, so the comparison is deterministic on glibc. The
 * primitive is ordinary in-process memory, so a plain memcmp is correct
 * here; only mailbox bytes are volatile.
 */
static inline uint8_t mcmini_mutex_is_static_initializer(
    const pthread_mutex_t *m) {
  static const pthread_mutex_t proto = PTHREAD_MUTEX_INITIALIZER;
  return memcmp(m, &proto, sizeof(pthread_mutex_t)) == 0
             ? MCMINI_PRIMITIVE_STATIC_INIT
             : MCMINI_PRIMITIVE_NOT_STATIC_INIT;
}

/** Report whether `c` is byte-equal to PTHREAD_COND_INITIALIZER. */
static inline uint8_t mcmini_cond_is_static_initializer(
    const pthread_cond_t *c) {
  static const pthread_cond_t proto = PTHREAD_COND_INITIALIZER;
  return memcmp(c, &proto, sizeof(pthread_cond_t)) == 0
             ? MCMINI_PRIMITIVE_STATIC_INIT
             : MCMINI_PRIMITIVE_NOT_STATIC_INIT;
}

/**
 * The offset of a flag byte within a mailbox payload.
 *
 * THE single place flag offsets come from (INIT-05): the flag block starts
 * after the `n_pointers`-pointer block, and `flag_index` selects the flag
 * in pointer order.
 */
static inline size_t mcmini_payload_flag_offset(size_t n_pointers,
                                                size_t flag_index) {
  return n_pointers * sizeof(void *) + flag_index;
}

/**
 * Store one flag byte into the mailbox payload.
 *
 * Goes through `memcpy_v`, the only sanctioned access to the volatile
 * mailbox bytes.
 */
static inline void mcmini_payload_write_flag(volatile uint8_t *cnts,
                                             size_t n_pointers,
                                             size_t flag_index, uint8_t flag) {
  memcpy_v(cnts + mcmini_payload_flag_offset(n_pointers, flag_index), &flag,
           sizeof(flag));
}

/**
 * Load one flag byte from the mailbox payload.
 *
 * The mirror image of `mcmini_payload_write_flag`, through `memcpy_v`.
 */
static inline uint8_t mcmini_payload_read_flag(const volatile uint8_t *cnts,
                                               size_t n_pointers,
                                               size_t flag_index) {
  uint8_t flag;
  memcpy_v(&flag, cnts + mcmini_payload_flag_offset(n_pointers, flag_index),
           sizeof(flag));
  return flag;
}

#ifdef __cplusplus
}
#endif  // extern "C"
