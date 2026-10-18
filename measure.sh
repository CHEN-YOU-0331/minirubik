#!/bin/sh
# measure.sh - 步驟七每次修改後執行:檢查 13 筆輸出和 C 相同,並量兩個單一狀態的指令數
# 用法(在 repo 根目錄):sh measure.sh
set -e
cat data.s solver.s > run.s
"$RIPES" --mode cli --src run.s -t asm --proc RV32_ISS --iret > out.txt
sed -n 's/^    \.byte .*# \([0-9]*\) -> [0-9]* moves: *\(.*\)$/\1: \2/p; s/^    \.byte .*# \([0-9]*\) invalid.*$/\1: invalid/p' data.s > expect.txt
if head -13 out.txt | diff -q - expect.txt > /dev/null; then
    echo "13 tests: asm == C, $(tail -1 out.txt) instructions"
else
    echo "13 tests: output differs from C"
    exit 1
fi
for st in 21345671111111 54721631111111; do
    host/ida5 --emit one.s $st > /dev/null
    cat one.s solver.s > run.s
    echo "$st: $("$RIPES" --mode cli --src run.s -t asm --proc RV32_ISS --iret | tail -1) instructions"
done
