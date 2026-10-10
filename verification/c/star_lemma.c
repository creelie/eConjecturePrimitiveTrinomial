/* star_lemma.c -- exhaustive checks of Section 4 of the paper, for words of length k <= K.
 *
 * A word x of length k is a bit mask: bit i-1 holds the i-th letter (1 = N, 0 = E).
 * B(x, y) is the parity of the number of positions i with x_i = y_i and w(x_{<i}) = w(y_{<i}),
 * which is the parity of the number of common edges of the two lattice paths.
 *
 *  1. Cell identity (Lemma 4.2): for every path p of length k and every unit square Q with lower
 *     left corner (x, y), x + y <= k - 2, the number of edges of p on the boundary of Q has the
 *     parity of V_p(x, y) + V_p(x + 1, y + 1), where V_p is the indicator of the vertices of p.
 *  2. Star lemma (Lemma 4.1): if w(a) = w(b) + 1, B(a, b) = k + 1 (mod 2) and B(a, c) = B(b, c)
 *     for every c whose weight is neither w(a) nor w(b), then (a, b) = (u1, u0) for a word u,
 *     or k = 2j + 1 >= 3 and (a, b) = (1(10)^j, 0(01)^j).
 *  3. Canonical pairs (Lemma 5.2): B(u1, c) + B(u0, c) = [w(c_{<k}) = w(u)] for all u and c.
 *
 * Usage: star_lemma [K]   (default K = 13, K <= 20).  Prints ALL OK when every check passes. */
#include <stdio.h>
#include <stdlib.h>

static int k;

static int B(unsigned x, unsigned y)
{
    int s = 0, d = 0;               /* d = w(x_{<i}) - w(y_{<i}) */
    for (int i = 0; i < k; i++) {
        int xi = (x >> i) & 1, yi = (y >> i) & 1;
        if (d == 0 && xi == yi) s ^= 1;
        d += xi - yi;
    }
    return s;
}

/* the point of path p at level l is (l - h, h) with h = w(p_{<=l}) */
static int height(unsigned p, int l) { return __builtin_popcount(p & ((1u << l) - 1)); }

/* does path p use the unit edge from (x, y) in direction dir (0 = E, 1 = N)? */
static int uses(unsigned p, int x, int y, int dir)
{
    int l = x + y;
    if (l >= k || height(p, l) != y) return 0;
    return (int)((p >> l) & 1) == dir;
}

static int visits(unsigned p, int x, int y)
{
    int l = x + y;
    return l <= k && height(p, l) == y;
}

int main(int argc, char **argv)
{
    int K = argc > 1 ? atoi(argv[1]) : 13;
    int failures = 0;
    if (K < 1 || K > 20) { fprintf(stderr, "K must lie in 1..20\n"); return 2; }

    for (k = 1; k <= K; k++) {
        unsigned N = 1u << k;
        int *wt = malloc(N * sizeof *wt);
        for (unsigned x = 0; x < N; x++) wt[x] = __builtin_popcount(x);

        /* 1. cell identity */
        long cells = 0, cellbad = 0;
        for (unsigned p = 0; p < N; p++)
            for (int x = 0; x <= k - 2; x++)
                for (int y = 0; x + y <= k - 2; y++) {
                    int e = uses(p, x, y, 0) + uses(p, x, y, 1)            /* bottom, left */
                          + uses(p, x, y + 1, 0) + uses(p, x + 1, y, 1);   /* top, right */
                    cells++;
                    if ((e & 1) != ((visits(p, x, y) + visits(p, x + 1, y + 1)) & 1)) cellbad++;
                }

        /* 2. star lemma */
        long canonical = 0, exceptional = 0, other = 0, rejected = 0;
        unsigned last = 1u << (k - 1), ea = 1, eb = 0;
        for (int i = 1; i < k; i++) { if (i % 2) ea |= 1u << i; else eb |= 1u << i; }
        for (unsigned a = 0; a < N; a++)
            for (unsigned b = 0; b < N; b++) {
                if (wt[a] != wt[b] + 1 || B(a, b) != ((k + 1) & 1)) continue;
                int ok = 1;
                for (unsigned c = 0; c < N && ok; c++)
                    if (wt[c] != wt[a] && wt[c] != wt[b] && B(a, c) != B(b, c)) ok = 0;
                if (!ok) { rejected++; continue; }
                int canon = (a & ~last) == (b & ~last) && (a & last) && !(b & last);
                int exc = k % 2 == 1 && k >= 3 && a == ea && b == eb;
                if (canon) canonical++;
                else if (exc) exceptional++;
                else { other++; fprintf(stderr, "k=%d: unexpected pair a=%x b=%x\n", k, a, b); }
            }

        /* 3. canonical pairs: f(c) = [w(c_{<k}) = w(u)] */
        long fbad = 0;
        for (unsigned u = 0; u < N / 2; u++)
            for (unsigned c = 0; c < N; c++) {
                int f = B(u | last, c) ^ B(u, c);
                if (f != (wt[c & ~last] == wt[u])) fbad++;
            }

        int expect_exc = k % 2 == 1 && k >= 3;
        int bad = cellbad || fbad || other || canonical != (long)(N / 2) || exceptional != expect_exc;
        printf("k=%2d  cells=%8ld bad=%ld  star: canonical=%6ld (2^(k-1)=%6u) exceptional=%ld (expected %d)"
               " other=%ld rejected=%8ld  canonical-pair formula bad=%ld%s\n",
               k, cells, cellbad, canonical, N / 2, exceptional, expect_exc, other, rejected, fbad,
               bad ? "  FAIL" : "");
        failures += bad;
        free(wt);
    }
    if (failures) { printf("FAILED\n"); return 1; }
    printf("ALL OK: Lemmas 4.1, 4.2 and 5.2 for every k <= %d\n", K);
    return 0;
}
