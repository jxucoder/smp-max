#!/bin/bash
i=$1
cnf="cubeL${i}.cnf"
kissat -q "$cnf" "cubeL${i}.drat" > /dev/null 2>&1
ks=$?
if [ $ks -ne 20 ]; then echo "cubeL${i}: SOLVE-FAIL exit=$ks"; exit 1; fi
dt=$(../../dt-src/drat-trim "$cnf" "cubeL${i}.drat" -L "cubeL${i}.lrat" 2>&1 | grep -c "s VERIFIED")
cl=$(../../cake_lpr-src/cake_lpr "$cnf" "cubeL${i}.lrat" 2>&1)
rm -f "cubeL${i}.drat" "cubeL${i}.lrat"
echo "cubeL${i}: kissat=UNSAT drat-trim=${dt} cake_lpr=${cl}"
