# AUD3: recompute Cramer rate I(x)=sup_l (l x - log I0(l)) used in NUM Remark res-heur, and Dirichlet Q.
from mpmath import mp, besseli, log, findroot, diff, acos, pi, ceil, mpf
mp.dps = 30
out = []
for x in [0.7, 0.8, 0.9]:
    f = lambda l: besseli(1, l)/besseli(0, l) - x
    l = findroot(f, 2.0)
    I = l*x - log(besseli(0, l))
    out.append(f"x={x}: lambda*={float(l):.5f} I(x)={float(I):.4f} slope I/ln10={float(I/log(10)):.4f}")
for eta in [0.3, 0.2, 0.1]:
    out.append(f"eta={eta}: 2pi/arccos(1-eta)={float(2*pi/acos(1-eta)):.3f} -> Q={int(ceil(2*pi/acos(1-eta)))}")
print("\n".join(out)); open('../out/aud3_ratefn.txt', 'w').write("\n".join(out)+"\n")
