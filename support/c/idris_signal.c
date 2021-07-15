#include "idris_signal.h"

#include <assert.h>
#include <limits.h>
#include <signal.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>

static_assert(ATOMIC_LONG_LOCK_FREE == 2,
              "when not lock free, atomic functions are not async-signal-safe");

#define N_SIGNALS 32
static atomic_long signal_count[N_SIGNALS];

void _collect_signal(int signum) {
    if (signum < 0 || signum >= N_SIGNALS) {
        abort();
    }

    long prev = atomic_fetch_add(&signal_count[signum], 1);
    if (prev == LONG_MAX) {
        // Practically impossible, but better crash explicitly
        fprintf(stderr, "signal count overflow\n");
        abort();
    }

#ifdef _WIN32
    // re-instate signal handler
    signal(signum, _collect_signal);
#endif
}

#ifndef _WIN32
static inline struct sigaction _simple_handler(void (*handler)(int)) {
    struct sigaction new_action;

    new_action.sa_handler = handler;
    sigemptyset(&new_action.sa_mask);
    new_action.sa_flags = 0;

    return new_action;
}
#endif

int ignore_signal(int signum) {
#ifdef _WIN32
    return signal(signum, SIG_IGN) == SIG_ERR ? -1 : 0;
#else
    struct sigaction handler = _simple_handler(SIG_IGN);
    return sigaction(signum, &handler, NULL);
#endif
}

int default_signal(int signum) {
#ifdef _WIN32
    return signal(signum, SIG_DFL) == SIG_ERR ? -1 : 0;
#else
    struct sigaction handler = _simple_handler(SIG_DFL);
    return sigaction(signum, &handler, NULL);
#endif
}

int collect_signal(int signum) {
#ifdef _WIN32
    return signal(signum, _collect_signal) == SIG_ERR ? -1 : 0;
#else
    struct sigaction handler = _simple_handler(_collect_signal);
    return sigaction(signum, &handler, NULL);
#endif
}

int handle_next_collected_signal() {
    for (int signum = 0; signum != N_SIGNALS; ++signum) {
        for (;;) {
            long count = atomic_load(&signal_count[signum]);
            if (count == 0) {
                break;
            }
            if (count < 0) {
                // Practically impossible, but better crash explicitly
                fprintf(stderr, "signal count overflow\n");
                abort();
            }
            if (atomic_compare_exchange_strong(&signal_count[signum], &count,
                                               count - 1)) {
                return signum;
            }
        }
    }
    return -1;
}

int raise_signal(int signum) {
    return raise(signum);
}

int send_signal(int pid, int signum) {
#ifdef _WIN32
    // TODO: ignores pid
    return raise_signal(signum);
#else
    return kill(pid, signum);
#endif
}

int sighup() {
#ifdef _WIN32
    return -1;
#else
    return SIGHUP;
#endif
}

int sigint() {
    return SIGINT;
}

int sigabrt() {
    return SIGABRT;
}

int sigquit() {
#ifdef _WIN32
    return -1;
#else
    return SIGQUIT;
#endif
}

int sigill() {
    return SIGILL;
}

int sigsegv() {
    return SIGSEGV;
}

int sigtrap() {
#ifdef _WIN32
    return -1;
#else
    return SIGTRAP;
#endif
}

int sigfpe() {
    return SIGFPE;
}

int sigusr1() {
#ifdef _WIN32
    return -1;
#else
    return SIGUSR1;
#endif
}

int sigusr2() {
#ifdef _WIN32
    return -1;
#else
    return SIGUSR2;
#endif
}
