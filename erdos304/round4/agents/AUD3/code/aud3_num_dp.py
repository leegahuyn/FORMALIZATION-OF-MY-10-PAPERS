# AUD3: independent recomputation of kappa_L for L <= 18 by two methods written from scratch:
#  (A) 0/1 knapsack DP over DISTINCT proper divisors (min #terms), vectorised with old-value semantics;
#  (B) multiset BFS R_k = R_{k-1} + (D* u {0}) (repetition allowed).
# Compares A==B pointwise (dedup theorem for these L), H, histogram, a_c, shift identity (pointwise),
# against NUM's data/H_table_bfs.csv.  Also verifies the stated optimal representations for L=23,25.
import numpy as np, math, csv, os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
R = os.path.join(HERE, '..', '..', '..')
OUT = os.path.join(HERE, '..', 'out', 'aud3_num_dp.txt')
lines = []
def P(*a):
    s = " ".join(str(x) for x in a); print(s); sys.stdout.flush(); lines.append(s)

def primes(n): return [p for p in range(2, n+1) if all(p % q for q in range(2, int(p**0.5)+1))]
def lam(L): return math.lcm(*range(1, L+1))
def divs(n):
    ds = [1]
    m = n
    for p in primes(64):
        e = 0
        while m % p == 0: m //= p; e += 1
        ds = [d*p**k for d in ds for k in range(e+1)]
    assert m == 1
    return sorted(ds)

tab = {}
with open(os.path.join(R, 'agents', 'NUM', 'data', 'H_table_bfs.csv')) as fh:
    for row in csv.DictReader(fh): tab[int(row['L'])] = row

INF = 255
seen = {}
for L in range(2, 19):
    Lam = lam(L)
    if Lam in seen:
        H, hist, ac = seen[Lam]
    else:
        t0 = time.time()
        D = [d for d in divs(Lam) if d < Lam]
        # (A) 0/1 DP, distinct divisors
        k = np.full(Lam, INF, np.uint8); k[0] = 0
        for d in sorted(D, reverse=True):
            cand = k[:-d].astype(np.int16) + 1          # old values (temp copy)
            np.minimum(k[d:], np.minimum(cand, INF).astype(np.uint8), out=k[d:])
        # (B) multiset BFS
        kb = np.full(Lam, INF, np.uint8); kb[0] = 0
        Rk = np.zeros(Lam, bool); Rk[0] = True; lev = 0
        while not Rk.all():
            lev += 1
            new = Rk.copy()
            for d in D: new[d:] |= Rk[:-d]
            kb[new & ~Rk] = lev; Rk = new
        same = np.array_equal(k, kb)
        H = int(k.max()); hist = [int((k == c).sum()) for c in range(1, H+1)]
        ac = [int(np.argmax(k == c)) for c in range(1, H+1)]
        half = Lam//2; b = np.arange(half)
        shift = bool(np.all(k[half:].astype(int) == 1 + k[:half].astype(int)))
        lowmax = int(k[:half].max())
        top_only_upper = bool((k[:half] < H).all())
        seen[Lam] = (H, hist, ac)
        P(f"L={L} Lam={Lam} tau={len(D)+1}: distinct-DP == multiset-BFS pointwise: {same}; H={H} hist={hist} a_c={ac}; "
          f"shift kappa(Lam/2+b)=1+kappa(b) for all b: {shift}; H==1+max_lower: {H==1+lowmax}; kappa=H only in upper half: {top_only_upper}  ({time.time()-t0:.1f}s)")
    row = tab[L]
    ok = (int(row['H']) == H and [int(x) for x in row['hist'].split()] == hist and [int(x) for x in row['a_c'].split()] == ac)
    P(f"   NUM table row L={L}: H={row['H']} agrees(H,hist,a_c)={ok}")

# ---- representations stated in NUM frag
P("--- stated optimal representations")
def check(L, a, ms, label):
    Lam = lam(L); terms = []
    for m in ms:
        assert Lam % m == 0, (L, m); terms.append(Lam//m)
    s = sum(terms)
    P(f"  L={L} {label}: a={a} sum={s} equal={s==a} all terms divide Lam and are proper: "
      f"{all(Lam % t == 0 and t < Lam for t in terms)} distinct={len(set(terms))==len(terms)} #terms={len(terms)}")
check(23, 3716552837, [2, 6, 38, 874, 134596, 20996976, 2677114440], 'a_7')
check(23, 1039438397, [6, 38, 874, 134596, 20996976, 2677114440], 'a_6')
for a, ts in [(25, [24, 1]), (5671, [5610, 60, 1]), (2486867, [2451570, 35190, 105, 2]),
              (110265329, [104984880, 5249244, 31122, 80, 3])]:
    Lam = lam(23)
    P(f"  L=23 a={a}: sum ok={sum(ts)==a} divisors={all(Lam % t == 0 for t in ts)} distinct={len(set(ts))==len(ts)}")
check(25, 26577893791, [2, 3, 7, 63, 1400, 278460, 66927861, 5354228880], 'a_8')
check(25, 13192321591, [3, 7, 63, 1400, 278460, 66927861, 5354228880], 'a_7')
Lam25 = lam(25); Lam23 = lam(23)
P(f"  Lam23={Lam23} Lam25={Lam25} Lam23/2+a6(23)={Lam23//2+1039438397} ; Lam25/2+a7(25)={Lam25//2+13192321591}")
P(f"  66927861 = {66927861} factor check: {[p for p in primes(30) if 66927861 % p == 0]}")
open(OUT, 'w').write("\n".join(lines)+"\n")
