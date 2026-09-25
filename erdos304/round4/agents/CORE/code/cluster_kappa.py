# CORE barrier II numerical illustration.
# For D = proper divisors of Lam_L, build D'' = cell-clustered set at resolution rho
# (same counts in every cell [(1+rho)^j,(1+rho)^{j+1}), elements moved to the left end of the cell,
# D'' = D below X0), and compute kappa(D'') = least k with k(D''u{0}) covering [0,Lam).
# Also the GH-barrier set D' (geometric progression with ratio 1/(1-delta/2) above X0).
import sys, math
import numpy as np

def lam(L):
    x = 1
    for i in range(2, L+1):
        x = x*i//math.gcd(x, i)
    return x

def divisors(n):
    ds = []
    d = 1
    while d*d <= n:
        if n % d == 0:
            ds.append(d)
            if d*d != n: ds.append(n//d)
        d += 1
    return sorted(ds)

def kappa(A, N, kmax=60):
    R = np.zeros(N, dtype=bool); R[0] = True
    F = R.copy()
    A = [a for a in A if 0 < a < N]
    for k in range(1, kmax+1):
        NX = np.zeros(N, dtype=bool)
        for a in A:
            NX[a:] |= F[:N-a]
        newF = NX & ~R
        R |= newF
        F = newF
        if R.all(): return k
        if not F.any(): return None
    return None

def clustered(D, N, rho, X0):
    out = set(d for d in D if d < X0)
    cells = {}
    for d in D:
        if d < X0: continue
        j = int(math.floor(math.log(d)/math.log(1+rho) + 1e-12))
        # guard floating error
        while (1+rho)**j > d: j -= 1
        while (1+rho)**(j+1) <= d: j += 1
        cells.setdefault(j, []).append(d)
    for j, lst in cells.items():
        y = max(X0, math.ceil((1+rho)**j))
        for i in range(len(lst)):
            out.add(y+i)
    return sorted(out)

def gp(D, N, delta, X0):
    out = set(d for d in D if d < X0)
    j = 0
    while True:
        z = int(math.floor(X0*(1-delta/2)**(-j)))
        if z >= N: break
        out.add(z); j += 1
    return sorted(out)

L = int(sys.argv[1]) if len(sys.argv) > 1 else 13
N = lam(L); D = [d for d in divisors(N) if d < N]
print(f"L={L} Lam={N} |D*|={len(D)} H(L)=kappa(D*)={kappa(D, N)}")
for X0 in [1, L]:
    for rho in [1.0, 0.5, 0.25, 0.1, 0.05, 0.02]:
        Dc = clustered(D, N, rho, X0)
        print(f"  cell-clustered X0={X0} rho={rho}: |D''|={len(Dc)} kappa={kappa(Dc, N)}")
for X0 in [8, 16, 64]:
    for delta in [0.5, 0.25, 0.1, 0.05]:
        if X0 < 2/delta: continue
        Dg = gp(D, N, delta, X0)
        print(f"  GH-set X0={X0} delta={delta}: |D'|={len(Dg)} kappa={kappa(Dg, N)}")
