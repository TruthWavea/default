/*
 * mols3_search.c -- decide whether a Latin square L of order n <= 10 belongs to a set
 * of three mutually orthogonal Latin squares, and search over many squares.
 *
 * Criterion.  L lies in a triple (L, L2, L3) of MOLS iff the n*n cells admit
 * two partitions P = {T_1..T_n}, Q = {U_1..U_n} into transversals of L with
 * |T_a ∩ U_b| = 1 for all a, b (L2 = index of the T containing a cell,
 * L3 = index of the U).  Equivalently: for some orthogonal mate L2 of L
 * (a partition P), the "common transversals" C(P) = { U : |U ∩ T| = 1 for
 * all T in P } contain a partition of the cells.
 *
 * For each square we enumerate ALL transversals, ALL mates (exact covers of
 * the cells by transversals), and for each mate solve the exact cover problem
 * on C(P).  This is a complete decision procedure for the given square
 * (unless the mate cap is hit, which is reported).
 *
 * Near-miss statistics: nu(P) = maximum number of pairwise disjoint common
 * transversals of the pair (L, L2) (nu = n means a triple); and, over all pairs
 * of stored mates L2, L3 of L, the maximum number of distinct ordered pairs
 * (L2(i,j), L3(i,j)) (n*n means a triple).
 *
 * build:  gcc -O3 -march=native -o mols3_search mols3_search.c -lm
 * usage:
 *   mols3_search group NAME             validation squares: Z7, Z8, Z9, Z10, Z3xZ3, Z2^3, D5
 *   mols3_search file FILE              test squares read from FILE (n, then n rows, repeated)
 *   mols3_search gen SEED COUNT         print COUNT random squares of order 10
 *   mols3_search random SEED SECONDS    random squares of order 10 (Jacobson-Matthews chain)
 *   mols3_search prolong NAME K         prolongations of the order-9 table NAME (Z9, Z3xZ3)
 *                                       by its transversals; K squares (distinct counts)
 *   mols3_search tclimb SEED SECONDS T  annealing on the number of transversals, testing
 *                                       squares with more than T transversals
 *   mols3_search climb SEED SECONDS     experimental hill climbing (not used in the report)
 * environment:
 *   MATE_CAP=m   stop the mate enumeration of a square after m mates (reported as capped)
 *   NOSTOP=1     keep counting after a triple has been found (validation runs)
 *   ALL=1        prolong: test every prolongation, not one per transversal count
 *   TEMP=t       tclimb: annealing temperature
 * A triple, if found, is printed and written to TRIPLE_<tag>.txt; check it with
 * verify_10_4.py.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <math.h>

#define MAXN 10
#define MAXT 40000
#define MAXW ((MAXT + 63) / 64)
#define MAXM 1024            /* max size of C(P) handled by the clique code */

typedef struct { uint64_t w[2]; } cellset;

static int n, ncell;
static int L[MAXN][MAXN];
static int nt;
static uint8_t tcol[MAXT][MAXN];
static cellset tmask[MAXT];
static cellset fullmask;
static uint64_t *one;        /* one[a*words + ...]: bit b set iff |T_a ∩ T_b| = 1 */
static int words;

static long long mate_cap = 0;   /* 0 = unlimited */

static inline int cs_disjoint(const cellset *a, const cellset *b)
{
    return !((a->w[0] & b->w[0]) | (a->w[1] & b->w[1]));
}

static double now(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

/* ---------------------------------------------------------------- RNG --- */
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rng(void)
{
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs;
}
static inline int rnd(int k) { return (int)(rng() % (uint64_t)k); }

/* -------------------------------------------------------- transversals --- */
static uint8_t cur[MAXN];
static int tr_overflow;

static void tr_rec(int i, unsigned usedc, unsigned useds)
{
    if (i == n) {
        if (nt >= MAXT) { tr_overflow = 1; return; }
        memcpy(tcol[nt], cur, n);
        cellset m = {{0, 0}};
        for (int r = 0; r < n; r++) {
            int c = r * n + cur[r];
            m.w[c >> 6] |= 1ULL << (c & 63);
        }
        tmask[nt++] = m;
        return;
    }
    for (int j = 0; j < n; j++) {
        if (usedc >> j & 1) continue;
        int s = L[i][j];
        if (useds >> s & 1) continue;
        cur[i] = (uint8_t)j;
        tr_rec(i + 1, usedc | 1u << j, useds | 1u << s);
    }
}


/* count transversals only (no storage) */
static long long tcount;
static void tc_rec(int i, unsigned usedc, unsigned useds)
{
    if (i == n) { tcount++; return; }
    for (int j = 0; j < n; j++) {
        if (usedc >> j & 1) continue;
        int s = L[i][j];
        if (useds >> s & 1) continue;
        tc_rec(i + 1, usedc | 1u << j, useds | 1u << s);
    }
}
static long long count_transversals(void) { tcount = 0; tc_rec(0, 0, 0); return tcount; }

static void build_one(void)
{
    words = (nt + 63) / 64;
    one = realloc(one, (size_t)(nt ? nt : 1) * (words ? words : 1) * 8);
    memset(one, 0, (size_t)nt * words * 8);
    for (int a = 0; a < nt; a++) {
        uint64_t *ra = one + (size_t)a * words;
        for (int b = a + 1; b < nt; b++) {
            int k = __builtin_popcountll(tmask[a].w[0] & tmask[b].w[0])
                  + __builtin_popcountll(tmask[a].w[1] & tmask[b].w[1]);
            if (k == 1) {
                ra[b >> 6] |= 1ULL << (b & 63);
                one[(size_t)b * words + (a >> 6)] |= 1ULL << (a & 63);
            }
        }
    }
}

/* ------------------------------------------------- exact cover solver --- */
typedef struct xc {
    int *buf[MAXN + 1];
    int chosen[MAXN];
    void (*cb)(struct xc *);
    long long nsol, limit;
    int stop;
} xc_t;

static void xc_rec(xc_t *X, int depth, int ncand, cellset covered)
{
    if (depth == n) {
        X->nsol++;
        if (X->cb) X->cb(X);
        if (X->limit && X->nsol >= X->limit) X->stop = 1;
        return;
    }
    int *cand = X->buf[depth];
    int cnt[MAXN * MAXN];
    memset(cnt, 0, sizeof(int) * ncell);
    cellset cov = covered;
    for (int k = 0; k < ncand; k++) {
        int t = cand[k];
        cov.w[0] |= tmask[t].w[0];
        cov.w[1] |= tmask[t].w[1];
        const uint8_t *tc = tcol[t];
        for (int r = 0; r < n; r++) cnt[r * n + tc[r]]++;
    }
    if (cov.w[0] != fullmask.w[0] || cov.w[1] != fullmask.w[1]) return;
    int best = -1, bc = 1 << 30;
    for (int c = 0; c < ncell; c++) {
        if ((covered.w[c >> 6] >> (c & 63)) & 1) continue;
        if (cnt[c] < bc) { bc = cnt[c]; best = c; if (bc <= 1) break; }
    }
    int br = best / n, bcol = best % n;
    int *next = X->buf[depth + 1];
    for (int k = 0; k < ncand && !X->stop; k++) {
        int t = cand[k];
        if (tcol[t][br] != bcol) continue;
        int m = 0;
        for (int q = 0; q < ncand; q++) {
            int u = cand[q];
            if (cs_disjoint(&tmask[t], &tmask[u])) next[m++] = u;
        }
        if (m < n - depth - 1) continue;
        X->chosen[depth] = t;
        cellset nc = covered;
        nc.w[0] |= tmask[t].w[0];
        nc.w[1] |= tmask[t].w[1];
        xc_rec(X, depth + 1, m, nc);
    }
}

static void xc_alloc(xc_t *X, int cap)
{
    for (int d = 0; d <= MAXN; d++) X->buf[d] = malloc(sizeof(int) * cap);
}

/* ----------------------------------- max set of pairwise disjoint (nu) --- */
static int mc_m, mc_wd, mc_best;
static uint64_t mc_adj[MAXM][MAXM / 64];
static int mc_stack[MAXN + 1], mc_bestset[MAXN + 1];

static int bs_count(const uint64_t *R)
{
    int c = 0;
    for (int i = 0; i < mc_wd; i++) c += __builtin_popcountll(R[i]);
    return c;
}

static void mc_rec(uint64_t *R, int size)
{
    if (mc_best >= n) return;
    int cnt = bs_count(R);
    if (cnt == 0) {
        if (size > mc_best) { mc_best = size; memcpy(mc_bestset, mc_stack, sizeof(int) * size); }
        return;
    }
    uint64_t Rl[MAXM / 64], NR[MAXM / 64];
    memcpy(Rl, R, 8 * mc_wd);
    for (int i = 0; i < mc_wd; i++) {
        while (Rl[i]) {
            if (size + cnt <= mc_best) return;
            int v = i * 64 + __builtin_ctzll(Rl[i]);
            Rl[i] &= Rl[i] - 1;
            cnt--;
            for (int j = 0; j < mc_wd; j++) NR[j] = Rl[j] & mc_adj[v][j];
            mc_stack[size] = v;
            mc_rec(NR, size + 1);
        }
    }
}

/* returns nu and the chosen indices (into list) */
static int max_disjoint(const int *list, int m, int *out)
{
    if (m == 0) return 0;
    if (m > MAXM) m = MAXM;          /* lower bound only; flagged by caller */
    mc_m = m; mc_wd = (m + 63) / 64; mc_best = 0;
    for (int a = 0; a < m; a++) {
        memset(mc_adj[a], 0, 8 * mc_wd);
        for (int b = 0; b < m; b++)
            if (b != a && cs_disjoint(&tmask[list[a]], &tmask[list[b]]))
                mc_adj[a][b >> 6] |= 1ULL << (b & 63);
    }
    uint64_t R[MAXM / 64];
    memset(R, 0, sizeof R);
    for (int a = 0; a < m; a++) R[a >> 6] |= 1ULL << (a & 63);
    mc_rec(R, 0);
    for (int i = 0; i < mc_best; i++) out[i] = list[mc_bestset[i]];
    return mc_best;
}

/* ------------------------------------------------- per-square analysis --- */
typedef struct {
    int nt;
    long long nmates;
    int capped;
    int maxC;          /* max |C(P)| over mates */
    int bestnu;        /* max nu(P) over mates */
    long long nu_hist[MAXN + 1];
    int triple;
    int oversizeC;     /* some C(P) exceeded MAXM */
    int best_pairs;    /* max #distinct (L2,L3) symbol pairs over two mates L2 != L3 */
    long long pa, pb;  /* indices of that pair of mates */
} stats_t;

static stats_t S;
static xc_t XM, XQ;
static int clist[MAXT];
static int best_P[MAXN], best_D[MAXN];
static int triple_P[MAXN], triple_Q[MAXN];
static uint64_t acc[MAXW];
#define STORE_CAP 10000
static uint8_t (*mate_lab)[MAXN * MAXN];   /* cell -> index of transversal in mate */
static int (*mate_P)[MAXN];

static void q_cb(xc_t *X)
{
    memcpy(triple_Q, X->chosen, sizeof(int) * n);
}

static void mate_cb(xc_t *X)
{
    const int *P = X->chosen;
    memcpy(acc, one + (size_t)P[0] * words, 8 * words);
    for (int k = 1; k < n; k++) {
        const uint64_t *row = one + (size_t)P[k] * words;
        for (int i = 0; i < words; i++) acc[i] &= row[i];
    }
    int m = 0;
    for (int i = 0; i < words; i++) {
        uint64_t w = acc[i];
        while (w) { clist[m++] = i * 64 + __builtin_ctzll(w); w &= w - 1; }
    }
    if (m > S.maxC) S.maxC = m;
    if (m > MAXM) S.oversizeC = 1;
    if (m >= n) {
        cellset cov = {{0, 0}};
        for (int k = 0; k < m; k++) { cov.w[0] |= tmask[clist[k]].w[0]; cov.w[1] |= tmask[clist[k]].w[1]; }
        if (cov.w[0] == fullmask.w[0] && cov.w[1] == fullmask.w[1]) {
            memcpy(XQ.buf[0], clist, sizeof(int) * m);
            XQ.nsol = 0; XQ.limit = 1; XQ.stop = 0; XQ.cb = q_cb;
            cellset z = {{0, 0}};
            xc_rec(&XQ, 0, m, z);
            if (XQ.nsol) {
                S.triple++;
                memcpy(triple_P, P, sizeof(int) * n);
                if (!getenv("NOSTOP")) X->stop = 1;
            }
        }
    }
    int D[MAXN + 1];
    int nu = max_disjoint(clist, m, D);
    S.nu_hist[nu]++;
    if (nu > S.bestnu || (S.bestnu == 0 && nu == 0 && S.nmates == 0)) {
        S.bestnu = nu;
        memcpy(best_P, P, sizeof(int) * n);
        memcpy(best_D, D, sizeof(int) * nu);
    }
    if (S.nmates < STORE_CAP) {
        for (int a = 0; a < n; a++)
            for (int r = 0; r < n; r++) mate_lab[S.nmates][r * n + tcol[P[a]][r]] = (uint8_t)a;
        memcpy(mate_P[S.nmates], P, sizeof(int) * n);
    }
    S.nmates++;
    if (mate_cap && S.nmates >= mate_cap) { S.capped = 1; X->stop = 1; }
}

static void analyse(void)
{
    memset(&S, 0, sizeof S);
    S.bestnu = -1;
    nt = 0; tr_overflow = 0;
    tr_rec(0, 0, 0);
    if (tr_overflow) { fprintf(stderr, "too many transversals\n"); exit(1); }
    S.nt = nt;
    S.bestnu = 0;
    if (nt < n) return;
    build_one();
    for (int t = 0; t < nt; t++) XM.buf[0][t] = t;
    XM.nsol = 0; XM.limit = 0; XM.stop = 0; XM.cb = mate_cb;
    cellset z = {{0, 0}};
    xc_rec(&XM, 0, nt, z);
    long long m = S.nmates < STORE_CAP ? S.nmates : STORE_CAP;
    for (long long a = 0; a < m; a++) {
        const uint8_t *la = mate_lab[a];
        for (long long b = a + 1; b < m; b++) {
            const uint8_t *lb = mate_lab[b];
            uint64_t w0 = 0, w1 = 0;
            for (int c = 0; c < ncell; c++) {
                int k = la[c] * n + lb[c];
                if (k < 64) w0 |= 1ULL << k; else w1 |= 1ULL << (k - 64);
            }
            int d = __builtin_popcountll(w0) + __builtin_popcountll(w1);
            if (d > S.best_pairs) { S.best_pairs = d; S.pa = a; S.pb = b; }
        }
    }
}

/* --------------------------------------------------------------- output --- */
static void print_square(FILE *f, int M[MAXN][MAXN])
{
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) fprintf(f, "%d%s", M[i][j], j + 1 < n ? " " : "\n");
    }
}

static void partition_square(const int *P, int k, int M[MAXN][MAXN])
{
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) M[i][j] = -1;
    for (int a = 0; a < k; a++)
        for (int r = 0; r < n; r++) M[r][tcol[P[a]][r]] = a;
}

static void dump_triple(const char *tag)
{
    int L2[MAXN][MAXN], L3[MAXN][MAXN];
    partition_square(triple_P, n, L2);
    partition_square(triple_Q, n, L3);
    char fn[256];
    snprintf(fn, sizeof fn, "TRIPLE_%s.txt", tag);
    FILE *f = fopen(fn, "w");
    for (int pass = 0; pass < 2; pass++) {
        FILE *g = pass ? f : stdout;
        fprintf(g, "TRIPLE FOUND n=%d\n", n);
        print_square(g, L); fprintf(g, "\n");
        print_square(g, L2); fprintf(g, "\n");
        print_square(g, L3); fprintf(g, "\n");
    }
    fclose(f);
    fflush(stdout);
}

static void dump_best(FILE *f)
{
    int L2[MAXN][MAXN], L3[MAXN][MAXN];
    partition_square(best_P, n, L2);
    partition_square(best_D, S.bestnu, L3);
    fprintf(f, "n=%d transversals=%d mates=%lld%s maxC=%d nu=%d\n", n, S.nt, S.nmates,
            S.capped ? "(capped)" : "", S.maxC, S.bestnu);
    print_square(f, L); fprintf(f, "\n");
    print_square(f, L2); fprintf(f, "\n");
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
            if (L3[i][j] < 0) fprintf(f, ".");
            else fprintf(f, "%d", L3[i][j]);
            fprintf(f, "%s", j + 1 < n ? " " : "\n");
        }
    }
    fprintf(f, "\n");
    fflush(f);
}

static void dump_pairs(FILE *f)
{
    int L2[MAXN][MAXN], L3[MAXN][MAXN];
    partition_square(mate_P[S.pa], n, L2);
    partition_square(mate_P[S.pb], n, L3);
    fprintf(f, "n=%d transversals=%d mates=%lld distinct_pairs(L2,L3)=%d\n", n, S.nt, S.nmates, S.best_pairs);
    print_square(f, L); fprintf(f, "\n");
    print_square(f, L2); fprintf(f, "\n");
    print_square(f, L3); fprintf(f, "\n");
    fflush(f);
}

static void report(const char *tag)
{
    printf("%s n=%d T=%d mates=%lld%s maxC=%d nu=%d pairs=%d hist=[", tag, n, S.nt, S.nmates,
           S.capped ? "(capped)" : "", S.maxC, S.bestnu, S.best_pairs);
    for (int k = 0; k <= n; k++) printf("%lld%s", S.nu_hist[k], k < n ? "," : "");
    printf("]%s%s\n", S.triple ? " TRIPLE" : "", S.oversizeC ? " (C>MAXM: nu is a lower bound)" : "");
    fflush(stdout);
}

/* ----------------------------------------------------- Jacobson-Matthews --- */
static int8_t cube[MAXN][MAXN][MAXN];
static int improper, ir, ic, is_;

static void jm_from_L(void)
{
    memset(cube, 0, sizeof cube);
    for (int r = 0; r < n; r++) for (int c = 0; c < n; c++) cube[r][c][L[r][c]] = 1;
    improper = 0;
}

static void jm_to_L(void)
{
    for (int r = 0; r < n; r++) for (int c = 0; c < n; c++)
        for (int s = 0; s < n; s++) if (cube[r][c][s] == 1) L[r][c] = s;
}

static void jm_step(void)
{
    int r, c, s, r2, c2, s2;
    if (!improper) {
        do { r = rnd(n); c = rnd(n); s = rnd(n); } while (cube[r][c][s] != 0);
        for (r2 = 0; cube[r2][c][s] != 1; r2++) ;
        for (c2 = 0; cube[r][c2][s] != 1; c2++) ;
        for (s2 = 0; cube[r][c][s2] != 1; s2++) ;
    } else {
        int o[2] = {0, 0}, k;
        r = ir; c = ic; s = is_;
        k = 0; for (int x = 0; x < n; x++) if (cube[x][c][s] == 1) o[k++] = x;
        r2 = o[rnd(2)];
        k = 0; for (int x = 0; x < n; x++) if (cube[r][x][s] == 1) o[k++] = x;
        c2 = o[rnd(2)];
        k = 0; for (int x = 0; x < n; x++) if (cube[r][c][x] == 1) o[k++] = x;
        s2 = o[rnd(2)];
    }
    cube[r][c][s]++;  cube[r][c2][s]--;  cube[r2][c][s]--;  cube[r][c][s2]--;
    cube[r][c2][s2]++; cube[r2][c][s2]++; cube[r2][c2][s]++; cube[r2][c2][s2]--;
    if (cube[r2][c2][s2] < 0) { improper = 1; ir = r2; ic = c2; is_ = s2; }
    else improper = 0;
}

static void jm_walk(int steps)
{
    for (int i = 0; i < steps || improper; i++) jm_step();
    jm_to_L();
}

/* ------------------------------------------------------- built-in squares --- */
static void set_n(int nn)
{
    n = nn; ncell = n * n;
    fullmask.w[0] = fullmask.w[1] = 0;
    for (int c = 0; c < ncell; c++) fullmask.w[c >> 6] |= 1ULL << (c & 63);
}

static int is_latin(void)
{
    for (int i = 0; i < n; i++) {
        unsigned a = 0, b = 0;
        for (int j = 0; j < n; j++) { a |= 1u << L[i][j]; b |= 1u << L[j][i]; }
        if (a != (1u << n) - 1 || b != (1u << n) - 1) return 0;
    }
    return 1;
}

static void group_square(const char *name)
{
    if (!strcmp(name, "Z7") || !strcmp(name, "Z8") || !strcmp(name, "Z9") || !strcmp(name, "Z10")) {
        set_n(atoi(name + 1));
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) L[i][j] = (i + j) % n;
    } else if (!strcmp(name, "Z3xZ3")) {
        set_n(9);
        for (int i = 0; i < 9; i++) for (int j = 0; j < 9; j++)
            L[i][j] = ((i / 3 + j / 3) % 3) * 3 + (i % 3 + j % 3) % 3;
    } else if (!strcmp(name, "Z2^3")) {
        set_n(8);
        for (int i = 0; i < 8; i++) for (int j = 0; j < 8; j++) L[i][j] = i ^ j;
    } else if (!strcmp(name, "D5")) {     /* dihedral group of order 10 */
        set_n(10);
        /* element (a,e) = r^a s^e, a in Z5, e in {0,1}; index a + 5e */
        for (int x = 0; x < 10; x++) for (int y = 0; y < 10; y++) {
            int a = x % 5, e = x / 5, b = y % 5, f = y / 5;
            int c = e ? (a - b + 5) % 5 : (a + b) % 5;   /* r^a s^e r^b s^f = r^(a ± b) s^(e+f) */
            L[x][y] = c + 5 * ((e + f) % 2);
        }
    } else {
        fprintf(stderr, "unknown group %s\n", name); exit(1);
    }
}

/* ------------------------------------------------------------------ main --- */
int main(int argc, char **argv)
{
    if (argc < 3) { fprintf(stderr, "usage: see source\n"); return 1; }
    XM.cb = mate_cb; xc_alloc(&XM, MAXT);
    mate_lab = malloc(sizeof(*mate_lab) * STORE_CAP);
    mate_P = malloc(sizeof(*mate_P) * STORE_CAP);
    xc_alloc(&XQ, MAXT);
    if (getenv("MATE_CAP")) mate_cap = atoll(getenv("MATE_CAP"));

    if (!strcmp(argv[1], "group")) {
        group_square(argv[2]);
        if (!is_latin()) { fprintf(stderr, "not latin\n"); return 1; }
        double t0 = now();
        analyse();
        report(argv[2]);
        printf("time %.2fs\n", now() - t0);
        if (S.triple) dump_triple(argv[2]);
        return 0;
    }
    if (!strcmp(argv[1], "file")) {
        FILE *f = fopen(argv[2], "r");
        int nn, idx = 0;
        while (fscanf(f, "%d", &nn) == 1) {
            set_n(nn);
            for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (fscanf(f, "%d", &L[i][j]) != 1) return 1;
            if (!is_latin()) { fprintf(stderr, "square %d not latin\n", idx); return 1; }
            double t0 = now();
            analyse();
            char tag[64]; snprintf(tag, sizeof tag, "sq%d", idx);
            report(tag);
            printf("time %.2fs\n", now() - t0);
            if (S.triple) dump_triple(tag);
            dump_best(stdout);
            idx++;
        }
        return 0;
    }
    if (!strcmp(argv[1], "gen")) {             /* print COUNT random squares of order 10 */
        uint64_t seed = strtoull(argv[2], 0, 10);
        int count = argc > 3 ? atoi(argv[3]) : 1;
        rs ^= seed * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
        set_n(10);
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) L[i][j] = (i + j) % n;
        jm_from_L();
        for (int k = 0; k < count; k++) {
            jm_walk(5000);
            printf("%d\n", n);
            print_square(stdout, L);
        }
        return 0;
    }
    if (!strcmp(argv[1], "tclimb")) {          /* anneal on #transversals, fully test good squares */
        uint64_t seed = strtoull(argv[2], 0, 10);
        double limit = argc > 3 ? atof(argv[3]) : 60;
        int thresh = argc > 4 ? atoi(argv[4]) : 1500;
        if (!mate_cap) mate_cap = 5000000;
        rs ^= seed * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
        for (int i = 0; i < 100; i++) rng();
        set_n(10);
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) L[i][j] = (i + j) % n;
        jm_from_L(); jm_walk(5000);
        char bestfn[128];
        snprintf(bestfn, sizeof bestfn, "best_tclimb_%llu.txt", (unsigned long long)seed);
        double t0 = now(), lastrep = t0;
        long long steps = 0, tested = 0, complete = 0, withmates = 0, totmates = 0, restarts = 0;
        long long nu_tot[MAXN + 1] = {0};
        int global_nu = -1, global_C = -1, maxnt_seen = 0;
        int curL[MAXN][MAXN];
        long long curnt = count_transversals(), seg_best = 0, since = 0;
        double temp = getenv("TEMP") ? atof(getenv("TEMP")) : 3.0;
        while (now() - t0 < limit) {
            memcpy(curL, L, sizeof L);
            jm_from_L(); jm_walk(1);
            long long nnt = count_transversals();
            steps++;
            long long d = nnt - curnt;
            if (d >= 0 || (double)(rng() >> 11) / 9007199254740992.0 < exp((double)d / temp)) {
                curnt = nnt;
            } else {
                memcpy(L, curL, sizeof L);
            }
            if (curnt > maxnt_seen) maxnt_seen = (int)curnt;
            if (curnt > seg_best) {
                seg_best = curnt; since = 0;
                if (curnt >= thresh) {
                    analyse();
                    tested++;
                    if (!S.capped) complete++;
                    if (S.nmates) withmates++;
                    totmates += S.nmates;
                    for (int k = 0; k <= n; k++) nu_tot[k] += S.nu_hist[k];
                    report("TESTED");
                    if (S.triple) { char tag[64]; snprintf(tag, sizeof tag, "tclimb_%llu", (unsigned long long)seed); dump_triple(tag); return 0; }
                    if (S.nmates && (S.bestnu > global_nu || (S.bestnu == global_nu && S.maxC > global_C))) {
                        global_nu = S.bestnu; global_C = S.maxC;
                        FILE *bf = fopen(bestfn, "w"); dump_best(bf); fclose(bf);
                        report("NEWBEST");
                    }
                }
            } else if (++since > 200000) {
                jm_from_L(); jm_walk(5000);
                curnt = count_transversals(); seg_best = 0; since = 0; restarts++;
            }
            if (now() - lastrep > 60) {
                lastrep = now();
                printf("[tclimb %llu] t=%.0fs steps=%lld restarts=%lld cur_nt=%lld max_nt=%d tested=%lld complete=%lld withmates=%lld mates=%lld best_nu=%d best_C=%d nu_hist=[",
                       (unsigned long long)seed, lastrep - t0, steps, restarts, curnt, maxnt_seen, tested, complete, withmates, totmates, global_nu, global_C);
                for (int k = 0; k <= n; k++) printf("%lld%s", nu_tot[k], k < n ? "," : "");
                printf("]\n");
                fflush(stdout);
            }
        }
        printf("[tclimb %llu] FINAL t=%.0fs steps=%lld restarts=%lld max_nt=%d tested=%lld complete=%lld withmates=%lld mates=%lld best_nu=%d best_C=%d nu_hist=[",
               (unsigned long long)seed, now() - t0, steps, restarts, maxnt_seen, tested, complete, withmates, totmates, global_nu, global_C);
        for (int k = 0; k <= n; k++) printf("%lld%s", nu_tot[k], k < n ? "," : "");
        printf("]\n");
        return 0;
    }
    if (!strcmp(argv[1], "prolong")) {         /* prolongations of an order-9 square by its transversals */
        group_square(argv[2]);
        int K = argc > 3 ? atoi(argv[3]) : 5;
        if (n != 9) { fprintf(stderr, "need order 9\n"); return 1; }
        int base[MAXN][MAXN];
        memcpy(base, L, sizeof L);
        nt = 0; tr_rec(0, 0, 0);
        int nb = nt;
        static uint8_t bt[MAXT][MAXN];
        memcpy(bt, tcol, sizeof(uint8_t) * MAXN * nb);
        static long long cnt[MAXT];
        static int ord[MAXT];
        set_n(10);
        for (int t = 0; t < nb; t++) {
            for (int i = 0; i < 9; i++) for (int j = 0; j < 9; j++) L[i][j] = base[i][j];
            for (int i = 0; i < 9; i++) {
                int j = bt[t][i];
                L[i][9] = base[i][j]; L[9][j] = base[i][j]; L[i][j] = 9;
            }
            L[9][9] = 9;
            if (!is_latin()) { fprintf(stderr, "bug\n"); return 1; }
            cnt[t] = count_transversals();
            ord[t] = t;
        }
        for (int a = 0; a < nb; a++) for (int b = a + 1; b < nb; b++)
            if (cnt[ord[b]] > cnt[ord[a]]) { int x = ord[a]; ord[a] = ord[b]; ord[b] = x; }
        printf("base %s: %d transversals; prolongation transversal counts: max %lld min %lld\n", argv[2], nb, cnt[ord[0]], cnt[ord[nb-1]]);
        long long lastc = -1; int done = 0;
        for (int a = 0; a < nb && done < K; a++) {
            int t = ord[a];
            if (cnt[t] == lastc && !getenv("ALL")) continue;
            lastc = cnt[t];
            for (int i = 0; i < 9; i++) for (int j = 0; j < 9; j++) L[i][j] = base[i][j];
            for (int i = 0; i < 9; i++) { int j = bt[t][i]; L[i][9] = base[i][j]; L[9][j] = base[i][j]; L[i][j] = 9; }
            L[9][9] = 9;
            double t0 = now();
            analyse();
            char tag[64]; snprintf(tag, sizeof tag, "prolong_%s_t%d", argv[2], t);
            report(tag);
            printf("time %.1fs\n", now() - t0);
            if (S.triple) { dump_triple(tag); return 0; }
            if (!getenv("ALL")) {
                if (S.nmates) dump_best(stdout);
                if (S.nmates > 1) dump_pairs(stdout);
            }
            done++;
        }
        return 0;
    }
    if (!strcmp(argv[1], "random") || !strcmp(argv[1], "climb")) {
        int climb = !strcmp(argv[1], "climb");
        uint64_t seed = strtoull(argv[2], 0, 10);
        double limit = argc > 3 ? atof(argv[3]) : 60;
        rs ^= seed * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
        for (int i = 0; i < 100; i++) rng();
        set_n(10);
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) L[i][j] = (i + j) % n;
        jm_from_L();
        jm_walk(5000);
        char bestfn[128];
        snprintf(bestfn, sizeof bestfn, "best_%s_%llu.txt", argv[1], (unsigned long long)seed);
        double t0 = now(), lastrep = t0;
        long long squares = 0, complete = 0, withmates = 0, totmates = 0;
        long long nu_tot[MAXN + 1] = {0};
        int global_nu = -1, global_C = -1, global_pairs = 0;
        char pairfn[128];
        snprintf(pairfn, sizeof pairfn, "pairs_%s_%llu.txt", argv[1], (unsigned long long)seed);
        /* climbing state */
        int curL[MAXN][MAXN];
        double curscore = -1;
        long long since_improve = 0;
        while (now() - t0 < limit) {
            if (climb) {
                memcpy(curL, L, sizeof L);
                jm_from_L();
                jm_walk(1);
            } else {
                jm_walk(1500);
            }
            analyse();
            squares++;
            if (!S.capped) complete++;
            if (S.nmates) withmates++;
            totmates += S.nmates;
            for (int k = 0; k <= n; k++) nu_tot[k] += S.nu_hist[k];
            if (S.triple) { char tag[64]; snprintf(tag, sizeof tag, "%s_%llu", argv[1], (unsigned long long)seed); dump_triple(tag); return 0; }
            if (S.nmates && (S.bestnu > global_nu || (S.bestnu == global_nu && S.maxC > global_C))) {
                global_nu = S.bestnu; global_C = S.maxC;
                FILE *bf = fopen(bestfn, "w");
                dump_best(bf);
                fclose(bf);
                report("NEWBEST");
            }
            if (S.best_pairs > global_pairs) {
                global_pairs = S.best_pairs;
                FILE *pf = fopen(pairfn, "w"); dump_pairs(pf); fclose(pf);
                report("NEWPAIRS");
            }
            if (climb) {
                double sc = S.bestnu * 1e9 + (double)S.maxC * 1e6 + (S.nmates > 999 ? 999 : S.nmates) * 1e3 + (S.nt > 999 ? 999 : S.nt);
                if (sc >= curscore) {
                    if (sc > curscore) since_improve = 0;
                    curscore = sc;
                } else {
                    memcpy(L, curL, sizeof L);  /* reject */
                    since_improve++;
                }
                if (since_improve > 20000) {   /* restart */
                    jm_from_L(); jm_walk(5000);
                    curscore = -1; since_improve = 0;
                }
            }
            if (now() - lastrep > 60) {
                lastrep = now();
                printf("[%s %llu] t=%.0fs squares=%lld complete=%lld withmates=%lld mates=%lld best_nu=%d best_C=%d best_pairs=%d nu_hist=[",
                       argv[1], (unsigned long long)seed, lastrep - t0, squares, complete, withmates, totmates, global_nu, global_C, global_pairs);
                for (int k = 0; k <= n; k++) printf("%lld%s", nu_tot[k], k < n ? "," : "");
                printf("]\n");
                fflush(stdout);
            }
        }
        printf("[%s %llu] FINAL t=%.0fs squares=%lld complete=%lld withmates=%lld mates=%lld best_nu=%d best_C=%d best_pairs=%d nu_hist=[",
               argv[1], (unsigned long long)seed, now() - t0, squares, complete, withmates, totmates, global_nu, global_C, global_pairs);
        for (int k = 0; k <= n; k++) printf("%lld%s", nu_tot[k], k < n ? "," : "");
        printf("]\n");
        return 0;
    }
    fprintf(stderr, "unknown mode\n");
    return 1;
}
