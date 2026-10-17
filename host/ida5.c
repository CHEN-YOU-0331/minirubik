#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { C = 7, NP = 5040, NO = 729, N = NP * NO };

static const uint8_t source[3][C] = {
    {1, 4, 2, 0, 3, 5, 6}, {0, 1, 2, 4, 5, 6, 3}, {0, 2, 5, 3, 1, 4, 6}};
static const uint8_t twist[3][C] = {
    {1, 2, 0, 2, 1, 0, 0}, {0, 0, 0, 1, 2, 1, 2}, {0, 0, 0, 0, 0, 0, 0}};

typedef struct {
    uint8_t p[C], o[C];
} state_t;

static state_t quarter_turn(state_t s, int f)
{
    state_t r;
    for (int i = 0; i < C; i++) {
        int from = source[f][i];
        r.p[i] = s.p[from];
        r.o[i] = (s.o[from] + twist[f][i]) % 3;
    }
    return r;
}

static int rank_perm(const state_t *s)
{
    int p = 0;
    for (int i = 0; i < C; i++) {
        int smaller = 0;
        for (int j = i + 1; j < C; j++)
            smaller += s->p[j] < s->p[i];
        p = p * (C - i) + smaller;
    }
    return p;
}
static int rank_orient(const state_t *s)
{
    int o = 0;
    for (int i = 0; i < 6; i++)
        o = o * 3 + s->o[i];
    return o;
}
static void unrank_perm(int p, state_t *s)
{
    uint8_t avail[C] = {0, 1, 2, 3, 4, 5, 6};
    int f = 720;
    for (int i = 0; i < C; i++) {
        int q = p / f;
        p %= f;
        s->p[i] = avail[q];
        for (int j = q; j + 1 < C - i; j++)
            avail[j] = avail[j + 1];
        if (i < 5)
            f /= 6 - i;
    }
}
static void unrank_orient(int o, state_t *s)
{
    int sum = 0;
    for (int i = 6; i-- > 0;) {
        s->o[i] = o % 3;
        sum += s->o[i];
        o /= 3;
    }
    s->o[6] = (3 - sum % 3) % 3;
}

static uint16_t tp[3][NP], to[3][NO];
static uint8_t *dist;

static void build_transitions(void)
{
    state_t s;
    memset(&s, 0, sizeof s);
    for (int r = 0; r < NP; r++) {
        unrank_perm(r, &s);
        for (int f = 0; f < 3; f++) {
            state_t n = quarter_turn(s, f);
            tp[f][r] = rank_perm(&n);
        }
    }
    for (int i = 0; i < C; i++)
        s.p[i] = i;
    for (int r = 0; r < NO; r++) {
        unrank_orient(r, &s);
        for (int f = 0; f < 3; f++) {
            state_t n = quarter_turn(s, f);
            to[f][r] = rank_orient(&n);
        }
    }
}

static int full_bfs(void)
{
    uint32_t *queue = malloc(sizeof *queue * N), head = 0, tail = 1;
    uint32_t count[16] = {0};
    dist = malloc(N);
    memset(dist, 255, N);
    queue[0] = 0;
    dist[0] = 0;
    while (head < tail) {
        uint32_t x = queue[head++];
        int p = x / NO, o = x % NO;
        count[dist[x]]++;
        for (int f = 0; f < 3; f++) {
            int a = p, b = o;
            for (int t = 0; t < 3; t++) {
                a = tp[f][a];
                b = to[f][b];
                uint32_t y = (uint32_t) a * NO + b;
                if (dist[y] == 255) {
                    dist[y] = dist[x] + 1;
                    queue[tail++] = y;
                }
            }
        }
    }
    free(queue);
    for (int d = 0; d < 16 && count[d]; d++)
        printf("depth %2d: %u\n", d, count[d]);
    printf("reached %u of %d\n", tail, N);
    return tail == N;
}


/* ===================== 步驟 3:下界表 + IDA* ===================== */
static uint8_t dp[NP], dor[NO]; /* 各自投影圖上的精確距離 */

static void small_bfs(uint8_t *d, int n, const uint16_t *t0, const uint16_t *t1,
                      const uint16_t *t2)
{
    const uint16_t *t[3] = {t0, t1, t2};
    int *queue = malloc(sizeof *queue * n), head = 0, tail = 1;
    memset(d, 255, n);
    queue[0] = 0;
    d[0] = 0;
    while (head < tail) {
        int x = queue[head++];
        for (int f = 0; f < 3; f++) {
            int y = x;
            for (int k = 0; k < 3; k++) {
                y = t[f][y];
                if (d[y] == 255) {
                    d[y] = d[x] + 1;
                    queue[tail++] = y;
                }
            }
        }
    }
    free(queue);
}

static int h(int p, int o)
{
    return dp[p] > dor[o] ? dp[p] : dor[o];
}

static int check_tables(void)
{
    /* H2:每個表項都有被 BFS 走到(255 = 沒走到) */
    for (int i = 0; i < NP; i++)
        if (dp[i] == 255)
            return printf("H2 fail: dp[%d] unreached\n", i), 0;
    for (int i = 0; i < NO; i++)
        if (dor[i] == 255)
            return printf("H2 fail: dor[%d] unreached\n", i), 0;
    for (uint32_t x = 0; x < N; x++)
        if (dist[x] == 255)
            return printf("H2 fail: dist[%u] unreached\n", x), 0;
    puts("H2 ok: no unreached entry in dp, dor, dist");

    /* H1:下界在每一個狀態上都不高估 */
    uint64_t sum_h = 0, sum_d = 0;
    for (uint32_t x = 0; x < N; x++) {
        int hx = h(x / NO, x % NO);
        if (hx > dist[x])
            return printf("H1 fail: state %u h=%d dist=%d\n", x, hx, dist[x]), 0;
        sum_h += hx;
        sum_d += dist[x];
    }
    printf("H1 ok: h <= dist on all %d states (mean h %.2f, mean dist %.2f)\n", N,
           (double) sum_h / N, (double) sum_d / N);
    return 1;
}

static uint64_t nodes; /* 搜尋走進去的節點數 */
static int path[12];   /* 找到的走法:face * 3 + (轉數 - 1) */

/* (p,o) 能不能剛好再走 g 步解開?last = 上一步轉的面 */
static int dfs(int p, int o, int g, int last, int depth)
{
    nodes++;
    if (g == 0)
        return p == 0 && o == 0;
    for (int f = 0; f < 3; f++) {
        if (f == last) /* 同一面不連轉 */
            continue;
        int a = p, b = o;
        for (int t = 0; t < 3; t++) { /* 90、180、270 度 */
            a = tp[f][a];
            b = to[f][b];
            if (h(a, b) > g - 1) /* 剩下的步數不夠:剪掉 */
                continue;
            path[depth] = f * 3 + t;
            if (dfs(a, b, g - 1, f, depth + 1))
                return 1;
        }
    }
    return 0;
}

static int solve(int p, int o)
{
    for (int bound = h(p, o);; bound++) /* 界限從下界開始,每次加 1 */
        if (dfs(p, o, bound, -1, 0))
            return bound;
}

static const char *names[9] = {"R", "R2", "R'", "B", "B2", "B'", "D", "D2", "D'"};

static int verify(void)
{
    uint64_t total = 0, worst = 0, count = 0;
    int bad = 0;
    for (uint32_t x = 0; x < N; x++) {
        if (dist[x] != 11 && x % 997) /* 所有 d11 狀態,加上每 997 個取一個 */
            continue;
        int p = x / NO, o = x % NO;
        nodes = 0;
        int len = solve(p, o);
        for (int i = 0; i < len; i++) /* 照著解重播一次 */
            for (int k = 0; k <= path[i] % 3; k++) {
                p = tp[path[i] / 3][p];
                o = to[path[i] / 3][o];
            }
        if (len != dist[x] || p || o)
            bad++;
        total += nodes;
        count++;
        if (nodes > worst)
            worst = nodes;
    }
    printf("checked %llu states, mismatches %d, nodes mean %.0f worst %llu\n",
           (unsigned long long) count, bad, (double) total / count,
           (unsigned long long) worst);
    return bad == 0;
}


/* ===================== 步驟 4:為 RV32I 改寫搜尋 ===================== */
static uint64_t n_child;   /* 試過幾個 child(每試一個轉法算一次) */
typedef struct {
    int p, o, f, t;
} frame_t;
static frame_t fr[12];     /* fr[d]:深度 d 的節點,和它往下走的那一步 */

static int finish(int d)   /* 從 frame 把走法抄出來 */
{
    for (int i = 0; i <= d; i++)
        path[i] = fr[i].f * 3 + fr[i].t;
    return d + 1;
}

/* 4-A:資料不變,遞迴改成顯式的 frame */
static int solve_a(int p0, int o0)
{
    if (p0 == 0 && o0 == 0)
        return 0;
    for (int bound = h(p0, o0);; bound++) {
        int d = 0, g = bound, f = 0, t, last = -1, a, b;
        fr[0].p = p0;
        fr[0].o = o0;
    face:
        if (f == last)
            goto next_face;
        a = fr[d].p;
        b = fr[d].o;
        t = 0;
    turn:
        a = tp[f][a];
        b = to[f][b];
        n_child++;
        if (h(a, b) > g - 1)
            goto pruned;
        fr[d].f = f;
        fr[d].t = t;
        if (g == 1) /* h == 0 代表 p == 0 且 o == 0:解開了 */
            return finish(d);
        last = f; /* 往下走一層 */
        d++;
        g--;
        fr[d].p = a;
        fr[d].o = b;
        f = 0;
        goto face;
    pruned:
        if (++t < 3)
            goto turn;
    next_face:
        if (++f < 3)
            goto face;
        if (d == 0)
            continue; /* 根節點試完了:界限加 1 */
        a = fr[d].p;  /* 回上一層:從子節點的位置接著轉 */
        b = fr[d].o;
        d--;
        g++;
        f = fr[d].f;
        t = fr[d].t;
        last = d ? fr[d - 1].f : -1;
        goto pruned;
    }
}

/* 4-B:一次載入同時拿到下一個座標和它的下界 */
static uint32_t Ep[3][NP], Eo[3][NO];

static void build_entries(void)
{
    for (int f = 0; f < 3; f++) {
        for (int i = 0; i < NP; i++)
            Ep[f][i] = (uint32_t) tp[f][i] << 17 | ((1u << dp[tp[f][i]]) - 1);
        for (int i = 0; i < NO; i++)
            Eo[f][i] = (uint32_t) to[f][i] << 17 | ((1u << dor[to[f][i]]) - 1);
    }
}

static int solve_b(int p0, int o0)
{
    if (p0 == 0 && o0 == 0)
        return 0;
    for (uint32_t V0 = 0x7fu << (h(p0, o0) - 1);; V0 <<= 1) {
        uint32_t V = V0, ep, eo;
        int d = 0, f = 0, t, last = -1, a, b;
        fr[0].p = p0;
        fr[0].o = o0;
    face:
        if (f == last)
            goto next_face;
        a = fr[d].p;
        b = fr[d].o;
        t = 0;
    turn:
        ep = Ep[f][a];
        eo = Eo[f][b];
        a = ep >> 17;
        b = eo >> 17;
        n_child++;
        if ((ep | eo) & V) /* 取代 h(a, b) > g - 1 */
            goto pruned;
        fr[d].f = f;
        fr[d].t = t;
        if (V == 0x7f) /* 取代 g == 1 */
            return finish(d);
        last = f;
        d++;
        V >>= 1; /* 取代 g-- */
        fr[d].p = a;
        fr[d].o = b;
        f = 0;
        goto face;
    pruned:
        if (++t < 3)
            goto turn;
    next_face:
        if (++f < 3)
            goto face;
        if (d == 0)
            continue;
        a = fr[d].p;
        b = fr[d].o;
        d--;
        V <<= 1; /* 取代 g++ */
        f = fr[d].f;
        t = fr[d].t;
        last = d ? fr[d - 1].f : -1;
        goto pruned;
    }
}

/* 4-C:座標存 byte offset,兩個座標共用每個面的一塊表 */
enum { BLK = NP + NO, OBIAS = 4 * NP };
static uint32_t E[3][BLK]; /* E[f][0..NP-1]:perm;E[f][NP..]:orient */

static void build_block(void)
{
    for (int f = 0; f < 3; f++) {
        for (int i = 0; i < NP; i++)
            E[f][i] = (uint32_t) (4 * tp[f][i]) << 17 | (Ep[f][i] & 0x7f);
        for (int i = 0; i < NO; i++)
            E[f][NP + i] = (uint32_t) (OBIAS + 4 * to[f][i]) << 17 | (Eo[f][i] & 0x7f);
    }
}

static uint32_t load(int f, uint32_t off) /* 組語:add t0, base, off;lw t0, 0(t0) */
{
    return *(const uint32_t *) ((const char *) E[f] + off);
}

static int solve_c(int p0, int o0)
{
    uint32_t q0 = 4 * p0, r0 = OBIAS + 4 * o0;
    if (q0 == 0 && r0 == OBIAS)
        return 0;
    for (uint32_t V0 = 0x7fu << (h(p0, o0) - 1);; V0 <<= 1) {
        uint32_t V = V0, ep, eo, q, r;
        int d = 0, f = 0, t, last = -1;
        fr[0].p = q0;
        fr[0].o = r0;
    face:
        if (f == last)
            goto next_face;
        q = fr[d].p;
        r = fr[d].o;
        t = 0;
    turn:
        ep = load(f, q);
        eo = load(f, r);
        q = ep >> 17;
        r = eo >> 17;
        n_child++;
        if ((ep | eo) & V)
            goto pruned;
        fr[d].f = f;
        fr[d].t = t;
        if (V == 0x7f)
            return finish(d);
        last = f;
        d++;
        V >>= 1;
        fr[d].p = q;
        fr[d].o = r;
        f = 0;
        goto face;
    pruned:
        if (++t < 3)
            goto turn;
    next_face:
        if (++f < 3)
            goto face;
        if (d == 0)
            continue;
        q = fr[d].p;
        r = fr[d].o;
        d--;
        V <<= 1;
        f = fr[d].f;
        t = fr[d].t;
        last = d ? fr[d - 1].f : -1;
        goto pruned;
    }
}

/* 用同一批狀態驗證一個版本;all = 1 時檢查全部狀態 */
static int check(const char *name, int (*solver)(int, int), int all)
{
    uint64_t c0 = n_child, worst = 0, count = 0;
    uint32_t worst_x = 0;
    int bad = 0;
    for (uint32_t x = 0; x < N; x++) {
        if (!all && dist[x] != 11 && x % 997)
            continue;
        int p = x / NO, o = x % NO;
        uint64_t before = n_child;
        int len = solver(p, o);
        for (int i = 0; i < len; i++)
            for (int k = 0; k <= path[i] % 3; k++) {
                p = tp[path[i] / 3][p];
                o = to[path[i] / 3][o];
            }
        if (len != dist[x] || p || o)
            bad++;
        if (n_child - before > worst) {
            worst = n_child - before;
            worst_x = x;
        }
        count++;
    }
    printf("%s: checked %llu, mismatches %d, child evals mean %.0f worst %llu (state %u)\n",
           name, (unsigned long long) count, bad, (double) (n_child - c0) / count,
           (unsigned long long) worst, worst_x);
    return bad == 0;
}

/* ===================== 步驟 5:輸出組語的資料段 ===================== */
/* 和 solver.c 的 parse_state 相同的規則:14 位數字、1..7 的排列、扭轉總和 % 3 == 0 */
static int parse(const char *a, state_t *s)
{
    unsigned seen = 0, sum = 0;
    if (strlen(a) != 14)
        return 0;
    for (int i = 0; i < C; i++) {
        unsigned p = (unsigned) (a[i] - '1'), o = (unsigned) (a[i + C] - '1');
        if (p >= C || o >= 3 || (seen >> p & 1))
            return 0;
        s->p[i] = p;
        s->o[i] = o;
        seen |= 1u << p;
        sum += o;
    }
    return sum % 3 == 0;
}

static int emit(const char *file, int n, char **states)
{
    FILE *out = fopen(file, "w");
    uint32_t checksum = 0;
    if (!out)
        return perror(file), 0;
    fprintf(out, "# generated by: ida5 --emit; do not edit\n");
    fprintf(out, ".data\n");
    fprintf(out, "ntests: .word %d\n", n);
    fprintf(out, "# each test, 16 B: 14 ASCII digits, expected length (255 = must be rejected), pad\n");
    fprintf(out, "tests:\n");
    for (int i = 0; i < n; i++) {
        const char *a = states[i];
        state_t s;
        int len = 255;
        if (strlen(a) != 14) { /* 每筆測試固定 16 bytes,長度不對放不進來 */
            fprintf(stderr, "test %s: must be 14 characters\n", a);
            fclose(out);
            return 0;
        }
        if (parse(a, &s))
            len = solve_c(rank_perm(&s), rank_orient(&s));
        fprintf(out, "    .byte "); /* 字元用數字寫,不依賴組譯器支援 .ascii */
        for (int k = 0; k < 14; k++)
            fprintf(out, "%d, ", a[k]);
        fprintf(out, "%d, 0    # %s", len, a);
        if (len == 255)
            fprintf(out, " invalid, must be rejected\n");
        else {
            fprintf(out, " -> %d moves:", len);
            for (int k = 0; k < len; k++)
                fprintf(out, " %s", names[path[k]]);
            fprintf(out, "\n");
        }
    }
    fprintf(out, "# E[f][i] = (next offset << 17) | thermometer(lower bound of next)\n");
    fprintf(out, "# 3 faces x %d words; perm offsets 0..%d, orient offsets %d..%d\n", BLK,
            4 * (NP - 1), OBIAS, OBIAS + 4 * (NO - 1));
    fprintf(out, "E:\n");
    for (int f = 0; f < 3; f++)
        for (int i = 0; i < BLK; i += 8) {
            fprintf(out, "    .word ");
            for (int j = i; j < i + 8 && j < BLK; j++) {
                fprintf(out, "0x%08x%s", E[f][j], (j + 1 < i + 8 && j + 1 < BLK) ? ", " : "\n");
                checksum += E[f][j];
            }
        }
    fclose(out);
    printf("wrote %s: %d tests, %d table words, checksum %d\n", file, n, 3 * BLK,
           (int32_t) checksum);
    printf("static data: ntests 4 + tests %d + E %zu = %zu B (budget 131072 B)\n", 16 * n,
           sizeof E, 4 + 16 * (size_t) n + sizeof E);
    return 1;
}

int main(int argc, char **argv)
{
    build_transitions();
    for (int f = 0; f < 3; f++) {
        for (int r = 0; r < NP; r++)
            if (tp[f][tp[f][tp[f][tp[f][r]]]] != r)
                return puts("tp: 4 turns != identity"), 1;
        for (int r = 0; r < NO; r++)
            if (to[f][to[f][to[f][to[f][r]]]] != r)
                return puts("to: 4 turns != identity"), 1;
    }
    for (int x = 0; x < N; x += 97) {
        state_t s;
        unrank_perm(x / NO, &s);
        unrank_orient(x % NO, &s);
        for (int f = 0; f < 3; f++) {
            state_t n = quarter_turn(s, f);
            if (rank_perm(&n) != tp[f][x / NO] || rank_orient(&n) != to[f][x % NO])
                return puts("tables disagree with quarter_turn"), 1;
        }
    }
    puts("transition tables ok");
    printf("tp[0][0..3] = %d %d %d %d\n", tp[0][0], tp[0][1], tp[0][2], tp[0][3]);
    printf("to[0][0..3] = %d %d %d %d\n", to[0][0], to[0][1], to[0][2], to[0][3]);
    if (!full_bfs())
        return 1;

    small_bfs(dp, NP, tp[0], tp[1], tp[2]);
    small_bfs(dor, NO, to[0], to[1], to[2]);
    int mp = 0, mo = 0;
    for (int i = 0; i < NP; i++)
        if (dp[i] > mp)
            mp = dp[i];
    for (int i = 0; i < NO; i++)
        if (dor[i] > mo)
            mo = dor[i];
    printf("max dp = %d, max dor = %d\n", mp, mo);
    if (!check_tables())
        return 1;

    build_entries();
    build_block();
    printf("tables: step 3 = %zu B, 4-C = %zu B (budget 131072 B)\n",
           sizeof tp + sizeof to + sizeof dp + sizeof dor, sizeof E);
    if (argc == 2 && !strcmp(argv[1], "--step4")) {
        int ok = check("4-A frames ", solve_a, 0);
        ok &= check("4-B entries", solve_b, 0);
        ok &= check("4-C offsets", solve_c, 0);
        return !ok;
    }
    if (argc >= 4 && !strcmp(argv[1], "--emit")) /* ./ida5 --emit OUT.s STATE... */
        return !emit(argv[2], argc - 3, argv + 3);
    if (argc == 2 && !strcmp(argv[1], "--verify-all"))
        return !check("4-C all    ", solve_c, 1);

    if (argc == 2) { /* ./ida 21345671111111:解單一狀態 */
        state_t s;
        for (int i = 0; i < C; i++) {   
            s.p[i] = argv[1][i] - '1';
            s.o[i] = argv[1][i + C] - '1';
        }
        nodes = 0;
        int len = solve(rank_perm(&s), rank_orient(&s));
        for (int i = 0; i < len; i++)
            printf("%s%s", i ? " " : "", names[path[i]]);
        printf("\n%d moves, %llu nodes\n", len, (unsigned long long) nodes);
        return 0;
    }
    return !verify();
}