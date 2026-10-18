/* ref.c - 步驟七的對照組:同一個演算法(solve_c)交給 gcc -O2 編譯
 *
 * 和 solver.s 用同一份 data.s、同樣的輸出格式、同樣從界限 1 開始,
 * 所以兩者在 Ripes 上的 --iret 可以直接比較。
 *
 *   riscv64-unknown-elf-gcc -O2 -march=rv32i -mabi=ilp32 -ffreestanding \
 *       -nostdlib -nostartfiles -Wl,--no-relax -o ref.elf ref.c ref_data.S
 *
 * -nostdlib 讓任何 __mulsi3、__divsi3、memcpy 的呼叫都變成連結錯誤,
 * 確保編譯出來的程式只用 RV32I 指令。
 */
#include <stdint.h>

extern const uint32_t E[];
extern const uint8_t tests[];
extern const int32_t ntests;

enum { NP = 5040, NO = 729, BLK = NP + NO, OBIAS = 4 * NP };

static void sys(int code, int arg)
{
    register int a0 asm("a0") = arg;
    register int a7 asm("a7") = code;
    asm volatile("ecall" : "+r"(a0) : "r"(a7) : "memory");
}
static void put_char(int c) { sys(11, c); }
static void put_str(const char *s)
{
    while (*s)
        put_char(*s++);
}

typedef struct {
    uint32_t q, r;
    int f, t;
} frame_t;
static frame_t fr[12];
static const uint32_t *const face_table[3] = {E, E + BLK, E + 2 * BLK};

static uint32_t load(int f, uint32_t off)
{
    return *(const uint32_t *) ((const char *) face_table[f] + off);
}

/* 和 host/ida5.c 的 solve_c 相同,只有兩處不同:界限從 1 開始(表裡沒有根節點
 * 的下界),以及超過 11 步時回傳 -1。回傳步數,走法留在 fr[0..步數-1]。 */
static int solve(uint32_t q0, uint32_t r0)
{
    if (q0 == 0 && r0 == OBIAS)
        return 0;
    for (uint32_t V0 = 0x7f; V0 != 0x7fu << 11; V0 <<= 1) {
        uint32_t V = V0, ep, eo, q, r;
        int d = 0, f = 0, t, last = -1;
        fr[0].q = q0;
        fr[0].r = r0;
    face:
        if (f == last)
            goto next_face;
        q = fr[d].q;
        r = fr[d].r;
        t = 0;
    turn:
        ep = load(f, q);
        eo = load(f, r);
        q = ep >> 17;
        r = eo >> 17;
        if ((ep | eo) & V)
            goto pruned;
        fr[d].f = f;
        fr[d].t = t;
        if (V == 0x7f)
            return d + 1;
        last = f;
        d++;
        V >>= 1;
        fr[d].q = q;
        fr[d].r = r;
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
        q = fr[d].q;
        r = fr[d].r;
        d--;
        V <<= 1;
        f = fr[d].f;
        t = fr[d].t;
        last = d ? fr[d - 1].f : -1;
        goto pruned;
    }
    return -1;
}

/* 檢查 14 位數字並算出兩個座標;不合法回傳 0。乘法全部用加法和移位。 */
static int parse(const uint8_t *a, uint32_t *q, uint32_t *r)
{
    unsigned seen = 0, sum = 0, P = 0, O = 0;
    for (int i = 0; i < 7; i++) {
        unsigned p = a[i] - '1', o = a[i + 7] - '1';
        if (p >= 7 || o >= 3 || (seen >> p & 1))
            return 0;
        seen |= 1u << p;
        sum += o;
        if (i < 6)
            O = O + (O << 1) + o;
    }
    while (sum >= 3)
        sum -= 3;
    if (sum)
        return 0;
    for (int i = 0; i < 7; i++) {
        unsigned smaller = 0, acc = 0;
        for (int j = i + 1; j < 7; j++)
            smaller += a[j] < a[i];
        for (int k = 7 - i; k > 0; k--) { /* P * (7 - i),用重複加法 */
            acc += P;
            /* 空的 asm 讓 gcc 看不出這是乘法;否則 -O2 會把整個迴圈
             * 換回 P * (7 - i),而 RV32I 沒有乘法,會變成呼叫 __mulsi3 */
            asm("" : "+r"(acc));
        }
        P = acc + smaller;
    }
    *q = P << 2;
    *r = OBIAS + (O << 2);
    return 1;
}

static int run(void)
{
    static const char face_name[3] = {'R', 'B', 'D'};
    int failures = 0;
    for (int n = 0; n < ntests; n++) {
        const uint8_t *a = tests + 16 * n;
        uint32_t q, r;
        for (int i = 0; i < 14; i++)
            put_char(a[i]);
        put_str(": ");
        int got;
        if (!parse(a, &q, &r)) {
            put_str("invalid");
            got = 255;
        } else {
            got = solve(q, r);
            if (got < 0) {
                put_str("no solution within 11 moves");
                failures++;
                put_char('\n');
                continue;
            }
            for (int i = 0; i < got; i++) {
                if (i)
                    put_char(' ');
                put_char(face_name[fr[i].f]);
                if (fr[i].t == 1)
                    put_char('2');
                else if (fr[i].t == 2)
                    put_char('\'');
            }
        }
        if (got != a[14]) {
            put_str(" <- MISMATCH");
            failures++;
        }
        put_char('\n');
    }
    put_str("failures: ");
    sys(1, failures);
    put_char('\n');
    return failures;
}

void _start(void)
{
    sys(93, run());
    for (;;)
        ;
}
