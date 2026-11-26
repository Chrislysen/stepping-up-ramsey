/* verify_affine.c -- a check of a colouring given by a table tau of cross-ratio values that uses less symmetry
   than a check through 0, 1 and infinity. It shares no code with the search programs or the Python checkers.

   Points: 0..q-1 and INF = q. For a < b < c < d the colour of {a,b,c,d} is tau[x] with
       x = (a-c)(b-d) / ((a-d)(b-c)) mod q   when d < q,       x = (a-c) / (b-c) mod q   when d = INF.
   Nothing is assumed about tau. The program
     1. goes through EVERY 4-subset of the q+1 points and compares its colour with the colour of its image under
        z -> z + 1 and under z -> g z (g the smallest primitive root; INF is fixed by both);
     2. goes through every set of S0 points through 0 and 1 for colour 0, and of S1 points for colour 1, growing sets
        point by point in increasing order and stopping a branch at the first 4-subset of the other colour.
   If step 1 finds no mismatch, both maps keep the colouring. They generate all maps z -> u z + v (u != 0), which move
   any two finite points onto 0 and 1, and every set of 5 or more points has two finite points. So step 2 then covers
   every set of S0 or S1 points of the line.

   usage:  verify_affine Q TAU.txt S0 S1 THREADS      TAU.txt: q characters; places 0 and 1 are ignored, the others 0/1
   prints  the counts and PASS or FAIL.   exit 0 PASS, 1 FAIL, 2 bad input. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "compat_threads.h"

static int q, g, T, S0, S1;
static int *inv;
static unsigned char *tau;
static unsigned long long r_sub[64], r_mt[64], r_mg[64], r_full[2][64], r_prev[2][64];

static inline int col4(int a, int b, int c, int d) {           /* a < b < c < d <= q */
    long long num, den;
    if (d == q) { num = a - c + q; den = b - c + q; }
    else { num = (long long)(a - c + q) * (b - d + q) % q; den = (long long)(a - d + q) * (b - c + q) % q; }
    return tau[(int)(num * inv[den] % q)];
}

static inline int col_any(int *p) {                            /* four different points in any order */
    for (int i = 1; i < 4; i++) { int v = p[i], j = i; while (j > 0 && p[j - 1] > v) { p[j] = p[j - 1]; j--; } p[j] = v; }
    return col4(p[0], p[1], p[2], p[3]);
}

static DWORD WINAPI invariance(LPVOID arg) {
    int t = (int)(intptr_t)arg;
    unsigned long long n = 0, mt = 0, mg = 0;
    for (int a = t; a <= q - 3; a += T)
        for (int b = a + 1; b <= q - 2; b++)
            for (int c = b + 1; c <= q - 1; c++)
                for (int d = c + 1; d <= q; d++) {
                    int c0 = col4(a, b, c, d), p[4] = {a, b, c, d}, s[4], m[4];
                    for (int i = 0; i < 4; i++) {
                        s[i] = p[i] == q ? q : (p[i] + 1 == q ? 0 : p[i] + 1);
                        m[i] = p[i] == q ? q : (int)((long long)g * p[i] % q);
                    }
                    n++;
                    mt += col_any(s) != c0;
                    mg += col_any(m) != c0;
                }
    r_sub[t] = n; r_mt[t] = mt; r_mg[t] = mg;
    return 0;
}

/* set[0..m-1] is increasing and starts with 0, 1; add points from..q; count sets of `size` points all in colour c */
static void grow(int c, int size, int *set, int m, int from, unsigned long long *full, unsigned long long *prev) {
    for (int z = from; z <= q; z++) {
        int ok = 1;
        for (int i = 0; i < m && ok; i++)
            for (int j = i + 1; j < m && ok; j++)
                for (int k = j + 1; k < m; k++)
                    if (col4(set[i], set[j], set[k], z) != c) { ok = 0; break; }
        if (!ok) continue;
        if (m + 1 == size) { (*full)++; continue; }
        if (m + 2 == size) (*prev)++;
        set[m] = z;
        grow(c, size, set, m + 1, z + 1, full, prev);
    }
}

static DWORD WINAPI cliques(LPVOID arg) {
    int t = (int)(intptr_t)arg;
    for (int c = 0; c < 2; c++) {
        int size = c == 0 ? S0 : S1, set[16] = {0, 1};
        unsigned long long full = 0, prev = 0;
        for (int p1 = 2 + t; p1 <= q; p1 += T) {               /* the first added point; {0,1,p1} has no 4-subset yet */
            set[2] = p1;
            grow(c, size, set, 3, p1 + 1, &full, &prev);
        }
        r_full[c][t] = full; r_prev[c][t] = prev;
    }
    return 0;
}

static void run_all(LPTHREAD_START_ROUTINE f) {
    HANDLE h[64];
    for (int t = 0; t < T; t++) { h[t] = CreateThread(NULL, 0, f, (LPVOID)(intptr_t)t, 0, NULL); SetThreadPriority(h[t], THREAD_PRIORITY_BELOW_NORMAL); }
    WaitForMultipleObjects((DWORD)T, h, TRUE, INFINITE);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: verify_affine Q TAU.txt S0 S1 THREADS\n"); return 2; }
    q = atoi(argv[1]); S0 = atoi(argv[3]); S1 = atoi(argv[4]); T = atoi(argv[5]);
    if (q < 7 || q > 46000 || T < 1 || T > 64 || S0 < 5 || S0 > 9 || S1 < 5 || S1 > 9) return 2;
    for (int d = 2; d * d <= q; d++) if (q % d == 0) { fprintf(stderr, "q must be prime\n"); return 2; }
    FILE *f = fopen(argv[2], "r");
    if (!f) { perror(argv[2]); return 2; }
    tau = malloc((size_t)q);
    for (int x = 0; x < q; x++) {
        int ch = fgetc(f);
        if (x >= 2 && ch != '0' && ch != '1') { fprintf(stderr, "TAU needs q characters\n"); return 2; }
        tau[x] = (unsigned char)(x >= 2 ? ch - '0' : 2);
    }
    fclose(f);
    inv = calloc((size_t)q, sizeof(int));
    for (int x = 1; x < q; x++) {                              /* x^(q-2) by repeated squaring */
        long long r = 1, b = x;
        for (int e = q - 2; e; e >>= 1) { if (e & 1) r = r * b % q; b = b * b % q; }
        inv[x] = (int)r;
    }
    for (g = 2;; g++) { int x = 1, k = 0; do { x = (int)((long long)x * g % q); k++; } while (x != 1); if (k == q - 1) break; }
    ULONGLONG t0 = GetTickCount64();
    run_all(invariance);
    unsigned long long n = 0, mt = 0, mg = 0;
    for (int t = 0; t < T; t++) { n += r_sub[t]; mt += r_mt[t]; mg += r_mg[t]; }
    printf("INVARIANCE q=%d g=%d: %llu 4-subsets (all of them), mismatches under z+1: %llu, under g*z: %llu   [%.0f s]\n",
           q, g, n, mt, mg, (double)(GetTickCount64() - t0) / 1000.0);
    fflush(stdout);
    run_all(cliques);
    unsigned long long full[2] = {0, 0}, prev[2] = {0, 0};
    for (int c = 0; c < 2; c++) for (int t = 0; t < T; t++) { full[c] += r_full[c][t]; prev[c] += r_prev[c][t]; }
    printf("COLOUR 0: sets of %d points through 0,1: %llu   (sets of %d points in colour 0 through 0,1 that were examined: %llu)\n", S0, full[0], S0 - 1, prev[0]);
    printf("COLOUR 1: sets of %d points through 0,1: %llu   (sets of %d points in colour 1 through 0,1 that were examined: %llu)\n", S1, full[1], S1 - 1, prev[1]);
    int pass = mt == 0 && mg == 0 && full[0] == 0 && full[1] == 0 && n == (unsigned long long)(q + 1) * q / 2 * (q - 1) / 3 * (q - 2) / 4;
    printf("%s%s   [%.0f s]\n", pass ? "PASS" : "FAIL", pass ? ": no such set on the q+1 points" : "", (double)(GetTickCount64() - t0) / 1000.0);
    return pass ? 0 : 1;
}
