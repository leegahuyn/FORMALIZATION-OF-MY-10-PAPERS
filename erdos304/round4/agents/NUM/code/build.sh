#!/bin/bash
# Build all C programs of agents/NUM (gcc 13, x86-64 AVX-512 machine).
cd "$(dirname "$0")"
gcc -O3 -march=native -fopenmp -Wno-misleading-indentation -o hbfs hbfs.c
gcc -O3 -march=native -fopenmp -Wno-misleading-indentation -Wno-format-truncation -o hbfs2 hbfs2.c
gcc -O3 -march=native -o dp01 dp01.c
gcc -O3 -march=native -ffast-math -o resscan resscan.c -lm
gcc -O3 -march=native -o mitm23 mitm23.c
gcc -O3 -march=native -o mitm mitm.c
# reproduce (main runs):
#   ./hbfs 23 -t 2 -c <ckdir> -o ../data/bfs/hbfs_L23            (108 s, 1.4 GB)
#   ./hbfs2 25 -t 2 -x 30 -c <ckdir> -o ../data/bfs/hbfs2_L25 -K <kapsmall>   (609 s, 4.4 GB)
#   ./hbfs 25 -t 2 -c <ckdir> -keep1 -o ../data/bfs/hbfs_L25      (659 s, 6.7 GB)
#   ./run_resscan.sh 120 <L list>;  python3 lll_res.py <L list>;  python3 res_analyze.py
#   python3 make_tables.py && python3 assemble_frag.py
