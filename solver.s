# solver.s - 步驟七最終版:optimal 2x2x2 solver, RV32I only, for Ripes
# 演算法和 host/ida5.c 的 solve_c 相同;資料(E 表、測試)來自 data.s
# 用法:cat data.s solver.s > run.s
#
# 和步驟六的差別(每項都用 --iret 量過):
#   7-A 三次轉動展開,轉到第幾次由程式位置表示,不再需要計數器
#   7-B 三個面也展開,每個面的表起點固定放在 s6、s7、s8
#   7-C 返回位址直接是「下一次轉動」的開頭,回上一層時 jr 過去,不必再跳一次
#
# 搜尋時的暫存器
#   s0  q    perm 座標的 byte offset(4 * perm rank)
#   s1  r    orient 座標的 byte offset(20160 + 4 * orient rank)
#   s4  V    剪枝 mask,0x7f << (剩下的步數 - 1)
#   s5  fp   目前節點的 frame:{q, r, 面, 返回位址}
#   s6  R 面的表(E)   s7 B 面的表(E + 23076)   s8 D 面的表(E + 46152)
#   s9  上一步轉的面(根節點為 0,不等於任何面)
#   s10 0x7f   s11 20160(解開時的 r)   t6 這一輪根節點的 V
# 測試迴圈
#   a5  目前這筆測試的位址   a6 剩幾筆   a4 失敗筆數   a3 找到的步數
.text
main:
    la   s6, E
    li   t0, 23076
    add  s7, s6, t0             # B 面的表
    add  s8, s7, t0             # D 面的表
    li   s10, 127
    li   s11, 20160
    la   a5, tests
    la   t0, ntests
    lw   a6, 0(t0)
    li   a4, 0

next_test:
    # ---- 印出這筆的 14 個字元和 ": " ----
    li   t0, 0
print_state:
    add  t1, a5, t0
    lbu  a0, 0(t1)
    li   a7, 11
    ecall
    addi t0, t0, 1
    li   t1, 14
    bne  t0, t1, print_state
    li   a0, 58                 # ':'
    ecall
    li   a0, 32                 # ' '
    ecall

    # ---- 第一輪:檢查每一位,順便算 orient rank 和扭轉總和 ----
    li   t0, 0                  # i
    li   t2, 0                  # O = orient rank
    li   t3, 0                  # seen = 已出現的角塊(bit mask)
    li   t4, 0                  # 扭轉總和
check_digit:
    add  a0, a5, t0
    lbu  a1, 0(a0)
    addi a1, a1, -49            # p = 字元 - '1'
    lbu  a2, 7(a0)
    addi a2, a2, -49            # o = 字元 - '1'
    sltiu t1, a1, 7             # 小於 '1' 會變成很大的 unsigned,一起擋掉
    beqz t1, invalid
    sltiu t1, a2, 3
    beqz t1, invalid
    srl  t1, t3, a1             # 這個角塊出現過了嗎
    andi t1, t1, 1
    bnez t1, invalid
    li   t1, 1
    sll  t1, t1, a1
    or   t3, t3, t1
    add  t4, t4, a2
    li   t1, 6
    beq  t0, t1, digit_done     # 第 7 個方向由總和決定,不算進 rank
    slli t1, t2, 1              # O = O * 3 + o
    add  t2, t2, t1
    add  t2, t2, a2
digit_done:
    addi t0, t0, 1
    li   t1, 7
    bne  t0, t1, check_digit
mod3:                           # 扭轉總和 % 3,總和最多 14,用減的
    li   t1, 3
    blt  t4, t1, mod3_done
    addi t4, t4, -3
    j    mod3
mod3_done:
    bnez t4, invalid

    # ---- 第二輪:Lehmer code 算 perm rank,P = P * (7 - i) + 後面比它小的個數 ----
    li   t0, 0                  # i
    li   t1, 0                  # P
lehmer_i:
    li   a0, 7
    sub  a0, a0, t0             # 乘數 7 - i,用重複加法
    mv   a1, t1
    li   t1, 0
lehmer_mul:
    add  t1, t1, a1
    addi a0, a0, -1
    bnez a0, lehmer_mul
    add  a0, a5, t0
    lbu  a1, 0(a0)              # p[i](直接比 ASCII,大小順序一樣)
    addi a2, t0, 1              # j
lehmer_j:
    li   a3, 7
    beq  a2, a3, lehmer_next
    add  a0, a5, a2
    lbu  a0, 0(a0)
    sltu a0, a0, a1             # p[j] < p[i]
    add  t1, t1, a0
    addi a2, a2, 1
    j    lehmer_j
lehmer_next:
    addi t0, t0, 1
    li   a3, 7
    bne  t0, a3, lehmer_i

    # ---- 座標轉成 byte offset,放進根節點的 frame ----
    slli s0, t1, 2              # q = 4 * P
    slli s1, t2, 2
    add  s1, s1, s11            # r = 20160 + 4 * O
    la   s5, frames
    sw   s0, 0(s5)
    sw   s1, 4(s5)
    li   a3, 0                  # 步數
    bnez s0, search
    beq  s1, s11, report        # 已經解開:0 步

    # ---- IDA*:三次轉動和三個面都展開 ----
    # 每次轉動後,沒被剪掉就「掉進」jal 往下一層;jal 存下的返回位址
    # 正好是下一次轉動(或下一個面)的開頭,回上一層時直接 jr 回去。
search:
    mv   t6, s10                # 界限從 1 開始:V0 = 0x7f
iterate:
    mv   s4, t6
    la   s5, frames
    li   s9, 0                  # 根節點沒有上一步
faceR:
    beq  s9, s6, faceB      # 同一面不連轉
    lw   s0, 0(s5)
    lw   s1, 4(s5)
R1:
    add  t0, s6, s0
    lw   t0, 0(t0)
    add  t1, s6, s1
    lw   t1, 0(t1)
    srli s0, t0, 17
    srli s1, t1, 17
    or   t0, t0, t1
    and  t0, t0, s4
    bnez t0, R2             # 被剪掉:直接試下一次
    jal  ra, enterR           # 沒被剪掉:往下一層,ra = R2
R2:
    add  t0, s6, s0
    lw   t0, 0(t0)
    add  t1, s6, s1
    lw   t1, 0(t1)
    srli s0, t0, 17
    srli s1, t1, 17
    or   t0, t0, t1
    and  t0, t0, s4
    bnez t0, R3             # 被剪掉:直接試下一次
    jal  ra, enterR           # 沒被剪掉:往下一層,ra = R3
R3:
    add  t0, s6, s0
    lw   t0, 0(t0)
    add  t1, s6, s1
    lw   t1, 0(t1)
    srli s0, t0, 17
    srli s1, t1, 17
    or   t0, t0, t1
    and  t0, t0, s4
    bnez t0, faceB             # 被剪掉:直接試下一次
    jal  ra, enterR           # 沒被剪掉:往下一層,ra = faceB
faceB:
    beq  s9, s7, faceD      # 同一面不連轉
    lw   s0, 0(s5)
    lw   s1, 4(s5)
B1:
    add  t0, s7, s0
    lw   t0, 0(t0)
    add  t1, s7, s1
    lw   t1, 0(t1)
    srli s0, t0, 17
    srli s1, t1, 17
    or   t0, t0, t1
    and  t0, t0, s4
    bnez t0, B2             # 被剪掉:直接試下一次
    jal  ra, enterB           # 沒被剪掉:往下一層,ra = B2
B2:
    add  t0, s7, s0
    lw   t0, 0(t0)
    add  t1, s7, s1
    lw   t1, 0(t1)
    srli s0, t0, 17
    srli s1, t1, 17
    or   t0, t0, t1
    and  t0, t0, s4
    bnez t0, B3             # 被剪掉:直接試下一次
    jal  ra, enterB           # 沒被剪掉:往下一層,ra = B3
B3:
    add  t0, s7, s0
    lw   t0, 0(t0)
    add  t1, s7, s1
    lw   t1, 0(t1)
    srli s0, t0, 17
    srli s1, t1, 17
    or   t0, t0, t1
    and  t0, t0, s4
    bnez t0, faceD             # 被剪掉:直接試下一次
    jal  ra, enterB           # 沒被剪掉:往下一層,ra = faceD
faceD:
    beq  s9, s8, node_done      # 同一面不連轉
    lw   s0, 0(s5)
    lw   s1, 4(s5)
D1:
    add  t0, s8, s0
    lw   t0, 0(t0)
    add  t1, s8, s1
    lw   t1, 0(t1)
    srli s0, t0, 17
    srli s1, t1, 17
    or   t0, t0, t1
    and  t0, t0, s4
    bnez t0, D2             # 被剪掉:直接試下一次
    jal  ra, enterD           # 沒被剪掉:往下一層,ra = D2
D2:
    add  t0, s8, s0
    lw   t0, 0(t0)
    add  t1, s8, s1
    lw   t1, 0(t1)
    srli s0, t0, 17
    srli s1, t1, 17
    or   t0, t0, t1
    and  t0, t0, s4
    bnez t0, D3             # 被剪掉:直接試下一次
    jal  ra, enterD           # 沒被剪掉:往下一層,ra = D3
D3:
    add  t0, s8, s0
    lw   t0, 0(t0)
    add  t1, s8, s1
    lw   t1, 0(t1)
    srli s0, t0, 17
    srli s1, t1, 17
    or   t0, t0, t1
    and  t0, t0, s4
    bnez t0, node_done             # 被剪掉:直接試下一次
    jal  ra, enterD           # 沒被剪掉:往下一層,ra = node_done
node_done:
    beq  s4, t6, deeper         # 根節點也試完了
    lw   s0, 0(s5)              # 回上一層:從子節點的位置接著轉
    lw   s1, 4(s5)
    addi s5, s5, -16
    slli s4, s4, 1
    lw   t0, 12(s5)             # 返回位址(同時代表面和第幾次)
    lw   s9, -8(s5)             # 祖父節點轉的面(根節點讀到 guard 的 0)
    jr   t0
enterR:
    sw   s6, 8(s5)              # 記下這一步:面、返回位址
    sw   ra, 12(s5)
    beq  s4, s10, found         # 最後一步且下界為 0:解開了
    addi s5, s5, 16             # 往下一層
    srli s4, s4, 1
    sw   s0, 0(s5)
    sw   s1, 4(s5)
    mv   s9, s6
    j    faceR
enterB:
    sw   s7, 8(s5)              # 記下這一步:面、返回位址
    sw   ra, 12(s5)
    beq  s4, s10, found         # 最後一步且下界為 0:解開了
    addi s5, s5, 16             # 往下一層
    srli s4, s4, 1
    sw   s0, 0(s5)
    sw   s1, 4(s5)
    mv   s9, s7
    j    faceR
enterD:
    sw   s8, 8(s5)              # 記下這一步:面、返回位址
    sw   ra, 12(s5)
    beq  s4, s10, found         # 最後一步且下界為 0:解開了
    addi s5, s5, 16             # 往下一層
    srli s4, s4, 1
    sw   s0, 0(s5)
    sw   s1, 4(s5)
    mv   s9, s8
    j    faceR
deeper:
    slli t6, t6, 1              # 界限加 1
    li   t0, 260096             # 0x7f << 11:超過 11 步代表程式有錯
    beq  t6, t0, unsolvable
    j    iterate

    # ---- 印出解:從根節點的 frame 走到目前的 frame ----
found:
    la   t0, frames
print_move:
    lw   t1, 8(t0)              # 面
    lw   t2, 12(t0)             # 返回位址
    beqz a3, no_space
    li   a0, 32
    li   a7, 11
    ecall
no_space:
    li   a0, 82                 # 'R'
    la   t3, R1
    beq  t1, s6, face_char
    li   a0, 66                 # 'B'
    la   t3, B1
    beq  t1, s7, face_char
    li   a0, 68                 # 'D'
    la   t3, D1
face_char:
    li   a7, 11
    ecall
    sub  t2, t2, t3             # 每次轉動佔 10 個指令 = 40 bytes:40 = 90 度,80 = 180 度,120 = 270 度
    li   t3, 40
    beq  t2, t3, move_done      # 90 度沒有後綴
    li   a0, 50                 # '2'
    li   t3, 80
    beq  t2, t3, suffix
    li   a0, 39                 # '\''
suffix:
    ecall
move_done:
    addi a3, a3, 1
    addi t0, t0, 16
    bleu t0, s5, print_move

    # ---- 和預期長度比對 ----
report:
    lbu  t0, 14(a5)
    beq  t0, a3, line_end
    la   a0, msg_wrong
    j    fail
invalid:
    la   a0, msg_invalid
    jal  ra, puts
    lbu  t0, 14(a5)
    li   t1, 255
    beq  t0, t1, line_end       # 本來就該被拒絕
    la   a0, msg_wrong
    j    fail
unsolvable:
    la   a0, msg_unsolved
fail:
    addi a4, a4, 1
    jal  ra, puts
line_end:
    li   a0, 10
    li   a7, 11
    ecall
    addi a5, a5, 16
    addi a6, a6, -1
    bnez a6, next_test

    la   a0, msg_failures
    jal  ra, puts
    mv   a0, a4
    li   a7, 1
    ecall
    li   a0, 10
    li   a7, 11
    ecall
    mv   a0, a4                 # exit code = 失敗筆數
    li   a7, 93
    ecall

puts:                           # 逐字元印字串(不印結尾的 0)
    mv   t0, a0
    li   a7, 11
puts_loop:
    lbu  a0, 0(t0)
    beqz a0, puts_done
    ecall
    addi t0, t0, 1
    j    puts_loop
puts_done:
    jr   ra

.data
frame_guard: .word 0, 0, 0, 0   # frames[-1]:讓根節點讀到「上一步的面」= 0
frames:      .zero 192          # 12 個 frame,每個 16 bytes
msg_invalid:  .string "invalid"
msg_wrong:    .string " <- MISMATCH"
msg_unsolved: .string "no solution within 11 moves"
msg_failures: .string "failures: "
