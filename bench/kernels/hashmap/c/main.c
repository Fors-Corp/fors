#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ---- open addressing table: int64 -> int64 ---- */
typedef struct {
    int64_t *keys;
    int64_t *vals;
    uint8_t *used;
    size_t cap;
    size_t count;
} IntMap;

static void im_init(IntMap *m, size_t cap) {
    m->cap = cap;
    m->count = 0;
    m->keys = calloc(cap, sizeof(int64_t));
    m->vals = calloc(cap, sizeof(int64_t));
    m->used = calloc(cap, sizeof(uint8_t));
}

static uint64_t mix64(uint64_t x) {
    x ^= x >> 33;
    x *= 0xff51afd7ed558ccdULL;
    x ^= x >> 33;
    x *= 0xc4ceb9fe1a85ec53ULL;
    x ^= x >> 33;
    return x;
}

static void im_grow(IntMap *m);

static void im_incr(IntMap *m, int64_t key) {
    if ((double)(m->count + 1) > 0.7 * (double)m->cap) im_grow(m);
    size_t mask = m->cap - 1;
    size_t idx = (size_t)(mix64((uint64_t)key) & mask);
    for (;;) {
        if (!m->used[idx]) {
            m->used[idx] = 1;
            m->keys[idx] = key;
            m->vals[idx] = 1;
            m->count++;
            return;
        }
        if (m->keys[idx] == key) {
            m->vals[idx] += 1;
            return;
        }
        idx = (idx + 1) & mask;
    }
}

static void im_grow(IntMap *m) {
    size_t old_cap = m->cap;
    int64_t *old_keys = m->keys;
    int64_t *old_vals = m->vals;
    uint8_t *old_used = m->used;

    size_t new_cap = m->cap * 2;
    im_init(m, new_cap);

    for (size_t i = 0; i < old_cap; i++) {
        if (old_used[i]) {
            size_t mask = m->cap - 1;
            size_t idx = (size_t)(mix64((uint64_t)old_keys[i]) & mask);
            while (m->used[idx]) idx = (idx + 1) & mask;
            m->used[idx] = 1;
            m->keys[idx] = old_keys[i];
            m->vals[idx] = old_vals[i];
            m->count++;
        }
    }
    free(old_keys);
    free(old_vals);
    free(old_used);
}

/* ---- open addressing table: string -> int64, FNV-1a hashing ---- */
typedef struct {
    char **keys;
    int64_t *vals;
    uint8_t *used;
    size_t cap;
    size_t count;
} StrMap;

static uint64_t fnv1a(const char *s) {
    uint64_t h = 1469598103934665603ULL;
    for (; *s; s++) {
        h ^= (unsigned char)*s;
        h *= 1099511628211ULL;
    }
    return h;
}

static void sm_init(StrMap *m, size_t cap) {
    m->cap = cap;
    m->count = 0;
    m->keys = calloc(cap, sizeof(char *));
    m->vals = calloc(cap, sizeof(int64_t));
    m->used = calloc(cap, sizeof(uint8_t));
}

static void sm_grow(StrMap *m);

static void sm_incr(StrMap *m, const char *key) {
    if ((double)(m->count + 1) > 0.7 * (double)m->cap) sm_grow(m);
    size_t mask = m->cap - 1;
    size_t idx = (size_t)(fnv1a(key) & mask);
    for (;;) {
        if (!m->used[idx]) {
            m->used[idx] = 1;
            m->keys[idx] = strdup(key);
            m->vals[idx] = 1;
            m->count++;
            return;
        }
        if (strcmp(m->keys[idx], key) == 0) {
            m->vals[idx] += 1;
            return;
        }
        idx = (idx + 1) & mask;
    }
}

static void sm_grow(StrMap *m) {
    size_t old_cap = m->cap;
    char **old_keys = m->keys;
    int64_t *old_vals = m->vals;
    uint8_t *old_used = m->used;

    size_t new_cap = m->cap * 2;
    sm_init(m, new_cap);

    for (size_t i = 0; i < old_cap; i++) {
        if (old_used[i]) {
            size_t mask = m->cap - 1;
            size_t idx = (size_t)(fnv1a(old_keys[i]) & mask);
            while (m->used[idx]) idx = (idx + 1) & mask;
            m->used[idx] = 1;
            m->keys[idx] = old_keys[i];
            m->vals[idx] = old_vals[i];
            m->count++;
        }
    }
    free(old_keys);
    free(old_vals);
    free(old_used);
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: %s N\n", argv[0]);
        return 1;
    }
    int64_t n = strtoll(argv[1], NULL, 10);

    IntMap im;
    im_init(&im, 16);
    StrMap sm;
    sm_init(&sm, 16);

    uint64_t x = 42;
    int64_t mod1 = n / 4 + 1;
    for (int64_t i = 0; i < n; i++) {
        x = (x * 48271ULL) % 2147483647ULL;
        int64_t key = (int64_t)(x % (uint64_t)mod1);
        im_incr(&im, key);
    }

    int64_t n2 = n / 4;
    int64_t mod2 = n / 16 + 1;
    char buf[32];
    for (int64_t i = 0; i < n2; i++) {
        x = (x * 48271ULL) % 2147483647ULL;
        int64_t num = (int64_t)(x % (uint64_t)mod2);
        snprintf(buf, sizeof(buf), "k%lld", (long long)num);
        sm_incr(&sm, buf);
    }

    uint64_t MOD = 1000000007ULL;
    uint64_t checksum = 0;
    for (size_t i = 0; i < im.cap; i++) {
        if (im.used[i]) {
            uint64_t k = (uint64_t)im.keys[i] % MOD;
            uint64_t c = (uint64_t)im.vals[i] % MOD;
            checksum = (checksum + (k * c) % MOD) % MOD;
        }
    }
    for (size_t i = 0; i < sm.cap; i++) {
        if (sm.used[i]) {
            int64_t num = strtoll(sm.keys[i] + 1, NULL, 10);
            uint64_t k = (uint64_t)num % MOD;
            uint64_t c = (uint64_t)sm.vals[i] % MOD;
            checksum = (checksum + (k * c) % MOD) % MOD;
        }
    }

    printf("%zu\n%zu\n%llu\n", im.count, sm.count, (unsigned long long)checksum);
    return 0;
}
