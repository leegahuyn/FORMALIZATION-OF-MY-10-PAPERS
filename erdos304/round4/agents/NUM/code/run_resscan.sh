#!/bin/bash
# Grid scan of the first resonance height tau*_{10}(L,eta), eta in {0.3,0.2,0.1}, for pools (L/2,L].
# One L per pool size M (the smallest prime L attaining that M).  Cap: $1 seconds per L.
# binary: resscan (compiled from resscan.c with gcc -O3 -march=native -ffast-math)
cd "$(dirname "$0")"
CAP=${1:-120}; shift
for L in "$@"; do nice -n 10 ./resscan $L 10 1e13 $CAP 0.3 0.2 0.1; done
