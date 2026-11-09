#!/bin/bash
# 4D SU(2) block-Poincare constant at fixed physical box L*sqrt(sigma) ~ 2.1-2.2 (a*sqrt(sigma) ~ 0.27, 0.19, 0.135
# at beta = 2.4, 2.5, 2.6), cubes at fixed n/L = 1/4, 3/8, 1/2. Selftest: n = L must give varpi = 1.
set -e
cd "$(dirname "$0")"
PY=python
gcc -O2 -o su2bp4d su2bp4d.c -lm
mkdir -p out; rm -f out/*.dat
{
echo "8 2.4 8 600 3 8 3 1 out/selftest_L8n8.dat"
for n in 2 3 4; do echo "8 2.4 $n 4000 5 12 4 $RANDOM out/b2.4_n${n}.dat"; done
for n in 3 6; do echo "12 2.5 $n 3000 5 12 4 $RANDOM out/b2.5_n${n}.dat"; done
for n in 4 6 8; do echo "16 2.6 $n 2500 5 12 4 $RANDOM out/b2.6_n${n}.dat"; done
} | xargs -P 9 -L 1 bash -c './su2bp4d $0 $1 $2 $3 $4 $5 $6 $7 > $8'
$PY analyze4d.py out/*.dat | tee out/summary.jsonl
