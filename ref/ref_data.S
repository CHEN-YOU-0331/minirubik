/* ref_data.S - 讓 C 對照組連結同一份 data.s(只把 label 宣告成全域) */
    .globl E, tests, ntests
    .include "data.s"
