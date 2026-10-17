# check_data.s - 步驟 5 的資料檢查:確認 Ripes 組譯出來的表和 C 一致
# 用法:cat data.s check_data.s > run.s,在 Ripes 上執行
.text
main:
    # (1) 把整張表加總,印出來和 C 印的 checksum 比對
    la   t0, E                  # t0 = 目前的位址
    li   t1, 17307              # 3 * 5769 個 word
    li   t2, 0                  # t2 = 總和
sum_loop:
    lw   t3, 0(t0)
    add  t2, t2, t3
    addi t0, t0, 4
    addi t1, t1, -1
    bnez t1, sum_loop
    mv   a0, t2
    li   a7, 1                  # 印出有號整數
    ecall
    li   a0, 10                 # 換行
    li   a7, 11
    ecall

    # (2) 逐筆印出測試資料:14 個字元、空格、預期長度
    la   t0, ntests
    lw   t1, 0(t0)              # t1 = 剩幾筆
    la   t0, tests              # t0 = 目前這筆的位址
test_loop:
    li   t2, 0                  # t2 = 第幾個字元
char_loop:
    add  t3, t0, t2
    lbu  a0, 0(t3)
    li   a7, 11                 # 印一個字元
    ecall
    addi t2, t2, 1
    li   t3, 14
    bne  t2, t3, char_loop
    li   a0, 32                 # 空格
    li   a7, 11
    ecall
    lbu  a0, 14(t0)             # 預期長度
    li   a7, 1
    ecall
    li   a0, 10
    li   a7, 11
    ecall
    addi t0, t0, 16             # 下一筆
    addi t1, t1, -1
    bnez t1, test_loop

    li   a0, 0
    li   a7, 93                 # 結束,exit code 0
    ecall