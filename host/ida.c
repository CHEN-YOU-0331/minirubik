/* ida.c - 步驟三:主機上的原型(不是目標平台的程式)
 *
 * 用遞迴的 IDA* 和 malloc 的 BFS 驗證演算法與下界,目標平台上兩者都不允許
 * (作業規定 no heap, no recursion);RV32I 版本見步驟四之後。
 *
 *   ./ida                  建表、H1/H2 檢查、抽樣驗證最優性
 *   ./ida 21345671111111   解單一狀態(不檢查輸入)
 *   gcc -DBREAK_H   ...    反向測試:下界故意高估,H1 必須失敗
 *   gcc -DBREAK_BFS ...    反向測試:小 BFS 少走兩個面,H2 必須失敗
 */     

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
#ifdef BREAK_BFS /* 反向測試:只走 R 面,有些表項會停在 255,H2 必須抓到 */
        for (int f = 0; f < 1; f++) {
#else
        for (int f = 0; f < 3; f++) {
#endif
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
    int v = dp[p] > dor[o] ? dp[p] : dor[o];
#ifdef BREAK_H /* 反向測試:故意讓下界高估 1,H1 必須抓到 */
    v += 1;
#endif
    return v;}

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
static uint64_t children; /* 試過的 child 數(每試一個轉法算一次,被剪掉的也算) */
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
            children++;
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
    uint64_t total = 0, worst = 0, count = 0, worst_c = 0;
    uint32_t worst_x = 0;
    int bad = 0;
    for (uint32_t x = 0; x < N; x++) {
        if (dist[x] != 11 && x % 997) /* 所有 d11 狀態,加上每 997 個取一個 */
            continue;
        int p = x / NO, o = x % NO;
        nodes = 0;
        children = 0;
        int len = solve(p, o);
        if (children > worst_c) {
            worst_c = children;
            worst_x = x;
        }
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
    state_t s;
    unrank_perm(worst_x / NO, &s);
    unrank_orient(worst_x % NO, &s);
    printf("worst children %llu at state ", (unsigned long long) worst_c);
    for (int i = 0; i < C; i++)
        printf("%d", s.p[i] + 1);
    for (int i = 0; i < C; i++)
        printf("%d", s.o[i] + 1);
    printf(" (rank %u, dist %d)\n", worst_x, dist[worst_x]);
    return bad == 0;
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

    if (argc == 2) { /* ./ida 21345671111111:解單一狀態 */
        state_t s;
        for (int i = 0; i < C; i++) {
            s.p[i] = argv[1][i] - '1';
            s.o[i] = argv[1][i + C] - '1';
        }
        nodes = 0;
        children = 0;
        int len = solve(rank_perm(&s), rank_orient(&s));
        for (int i = 0; i < len; i++)
            printf("%s%s", i ? " " : "", names[path[i]]);
        printf("\n%d moves, %llu nodes, %llu children\n", len, (unsigned long long) nodes,
               (unsigned long long) children);        return 0;
    }
    return !verify();
}