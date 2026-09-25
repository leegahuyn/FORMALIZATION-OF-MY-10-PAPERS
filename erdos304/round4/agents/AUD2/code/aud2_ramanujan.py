#!/usr/bin/env python3
"""AUD2: check pi(x)-pi(x/2) >= 4 for all real x in [29, X] (Ramanujan prime R_4 = 29),
and that it fails just below 29. Checking integer and half-integer x suffices (step changes only there)."""
import numpy as np
X = 2 * 10**6
s = np.ones(X + 1, dtype=bool); s[:2] = False
for p in range(2, int(X**0.5) + 1):
    if s[p]: s[p*p::p] = False
pi = np.cumsum(s)
xs = np.arange(29, X + 1)
v = pi[xs] - pi[xs // 2]          # pi(x/2) = pi(floor(x/2))
# half-integers x = m + 1/2: pi(x) = pi(m), pi(x/2) = pi(floor((2m+1)/4))
m = np.arange(29, X)
vh = pi[m] - pi[(2 * m + 1) // 4]
print("min over integer x in [29,2e6]:", int(v.min()), "; min over half-integers:", int(vh.min()))
print("x=28: pi(28)-pi(14) =", int(pi[28] - pi[14]))
