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
static int rank_perm(const state_t *s)      /* 0 .. 5039 */
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

static int rank_orient(const state_t *s)    /* 0 .. 728 */
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
    s->o[6] = (3 - sum % 3) % 3;   /* 第 7 個由總和決定 */
}
static uint16_t tp[3][NP], to[3][NO];

static void build_transitions(void)
{
    state_t s;
    memset(&s, 0, sizeof s);              /* o 全 0，只看排列 */
    for (int r = 0; r < NP; r++) {
        unrank_perm(r, &s);
        for (int f = 0; f < 3; f++) {
            state_t n = quarter_turn(s, f);
            tp[f][r] = rank_perm(&n);
        }
    }
    for (int i = 0; i < C; i++)           /* p 設成 identity，只看方向 */
        s.p[i] = i;
    for (int r = 0; r < NO; r++) {
        unrank_orient(r, &s);
        for (int f = 0; f < 3; f++) {
            state_t n = quarter_turn(s, f);
            to[f][r] = rank_orient(&n);
        }
    }
}
int main(void)
{
    build_transitions();

    /* 檢查 1:同一面轉四次要回到原處 */
    for (int f = 0; f < 3; f++) {
        for (int r = 0; r < NP; r++)
            if (tp[f][tp[f][tp[f][tp[f][r]]]] != r)
                return puts("tp: 4 turns != identity"), 1;
        for (int r = 0; r < NO; r++)
            if (to[f][to[f][to[f][to[f][r]]]] != r)
                return puts("to: 4 turns != identity"), 1;
    }

    /* 檢查 2:查表的結果要和「轉完整狀態再 rank」一致 */
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
    return 0;
}