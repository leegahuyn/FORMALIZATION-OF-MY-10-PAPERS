# AUD3: independent recomputation of every explicit constant in the VKGAP fragment.
# Output: ../out/aud3_vkgap_constants.txt
from mpmath import mp, mpf, sqrt, pi, log, exp, cos, sin, quad, inf, zeta, diff, e as E
import math, random
mp.dps = 30
out = []
def P(*a):
    s = " ".join(str(x) for x in a); print(s); out.append(s)

P("== Lemma pair / variance ==")
v = mpf('0.19')**2 * log(mpf('1.5'))**2
P("0.19^2 (log 1.5)^2 =", v, " >= v0=0.0059:", v >= mpf('0.0059'))
v0 = mpf('0.0059'); c2 = 2*v0/pi**2
P("c2 = 2 v0/pi^2 =", c2, " >0.00119:", c2 > mpf('0.00119'))
P("128/c2 = 64 pi^2/v0 =", 128/c2, " <1.08e5:", 128/c2 < 108000)
P("32/c2 =", 32/c2)
P("pi/log2 =", pi/log(2), "> 4")
# limiting variance of log U, U~Unif(1/2,1]
l2 = log(2)
varU = 2 - l2**2 - 2*l2 - (l2-1)**2
m1 = quad(lambda u: 2*log(u), [0.5, 1]); m2 = quad(lambda u: 2*log(u)**2, [0.5, 1])
P("Var(log U) closed form =", varU, "; by quadrature =", m2 - m1**2, " (VKGAP text says 0.03907; NUM says 0.039094)")

P("== log(y/2) >= log y/sqrt2 threshold ==")
P("y >= exp(log2/(1-1/sqrt2)) =", exp(l2/(1-1/sqrt(2))))

P("== Lemma Mellin ==")
kap = mpf(1)/20
def wt(s):
    # tilde w(s) = -(1/s) * 1/(kappa (s+1)) [ (1/2+k)^{s+1} - (1/2)^{s+1} - 1 + (1-k)^{s+1} ]
    return -(1/s)*(1/(kap*(s+1)))*((mpf(1)/2+kap)**(s+1) - (mpf(1)/2)**(s+1) - 1 + (1-kap)**(s+1))
def wt_direct(s):
    f = lambda u: (u-0.5)/kap if u < 0.5+kap else (1 if u <= 1-kap else (1-u)/kap)
    return quad(lambda u: f(u)*u**(s-1), [0.5, 0.5+kap, 1-kap, 1])
for s in [mpf(1), mpf(2)+3j, mpf('0.5')+7j, 1+4j]:
    P(" wt(s) closed vs direct at", s, ":", abs(wt(s)-wt_direct(s)))
P(" wt(1) =", wt_direct(mpf(1)), " (claimed 0.45)")
worst = 0
for sig in [0, 0.25, 0.5, 0.9, 1, 1.5, 2, 3]:
    for t in [0.1*k for k in range(1, 3000)]:
        s = mpf(sig) + 1j*mpf(t)
        r = abs(wt(s))/min(1, 80/mpf(t)**2)
        worst = max(worst, r)
P(" max_{grid} |wt(sig+it)|/min(1,80/t^2) over sig in [0,3], t in (0,300]:", worst, " (<=1 required)")
for sig in [mpf('0.5'), mpf('0.95'), mpf(2)]:
    I = 2*quad(lambda t: abs(wt(sig+1j*t)), [1e-12, 1, 10, 100, 1000, inf])
    P(" int |wt(%s+it)| dt =" % sig, I, " (<36; bound 4 sqrt 80 =", 4*sqrt(80), ")")
F = lambda t: (2-2**(-1j*t))/(1+1j*t)
worst = -1
for t in [0.01*k for k in range(-5000, 5001)]:
    worst = max(worst, abs(wt(1+1j*mpf(t))) - (abs(F(mpf(t)))/2 + kap))
P(" max_{|tau|<=50} (|wt(1+i tau)| - |F|/2 - kappa) =", worst, " (<=0 required)")
P(" 1.5/sqrt(17) =", mpf('1.5')/sqrt(17), "; margin 0.45-1.5/sqrt17-0.05 =", mpf('0.45')-mpf('1.5')/sqrt(17)-mpf('0.05'))
P(" (0.035)/0.51 =", mpf('0.035')/mpf('0.51'), " vs 1/15 =", mpf(1)/15)
P(" -zeta'(2)/zeta(2) =", -diff(zeta, 2)/zeta(2))
P(" 36/(2pi) =", 36/(2*pi), "; 2*1.05*80/(2pi) =", 2*mpf('1.05')*80/(2*pi), "; 0.6*160/(2pi) =", mpf('0.6')*160/(2*pi))
P(" RH: 36 e/(2 pi) =", 36*E/(2*pi), "; 2*1.5*80/(2pi) =", 2*mpf('1.5')*80/(2*pi))
P(" RH margin: 0.45-1.5/sqrt17-0.05-0.0004 =", mpf('0.45')-mpf('1.5')/sqrt(17)-mpf('0.05')-mpf('0.0004'), " /0.51 =",
  (mpf('0.45')-mpf('1.5')/sqrt(17)-mpf('0.05')-mpf('0.0004'))/mpf('0.51'))

P("== Remark F ==")
a = 2*l2**2
P(" a=2log^2 2 =", a, " sqrt((1+a)/2) =", sqrt((1+a)/2), " (1-a)/2 =", (1-a)/2)
g = lambda t: (5-4*cos(t*l2))/(1+t**2)
worst = -1
for t in [0.001*k for k in range(1, 100001)]:
    worst = max(worst, g(mpf(t)) - (a + (1-a)/(1+mpf(t)**2)))
P(" max_{0<t<=100} (|F|^2 - (a+(1-a)/(1+t^2))) =", worst, " (<=0 required)")
F1 = sqrt(g(1)); P(" |F(1)| =", F1, " 1-|F(1)| =", 1-F1, " ; frag threshold eta>0.0194 vs exact 1-|F(1)|")
mx = max(abs(F(mpf(t))) for t in [1+0.0005*k for k in range(0, 40000)])
P(" max_{1<=t<=21} |F| (grid 5e-4) =", mx)
P(" 3/sqrt(17) =", 3/sqrt(17), " |F(4)| =", abs(F(4)))

P("== Cumulant lemma (97/288) ==")
P(" 1/6+49/288 =", mpf(1)/6+mpf(49)/288, "=97/288=", mpf(97)/288, "; 7/48 =", mpf(7)/48)
random.seed(1); worst = 0
import cmath
for trial in range(20000):
    b = 1.0
    k = random.randint(2, 5)
    xs = [random.uniform(-1, 1) for _ in range(k)]; ps = [random.random() for _ in range(k)]
    sp = sum(ps); ps = [p/sp for p in ps]
    mu = sum(p*x for p, x in zip(ps, xs)); xs = [x-mu for x in xs]
    bb = max(abs(x) for x in xs)
    if bb == 0: continue
    s2 = sum(p*x*x for p, x in zip(ps, xs))
    tau = random.uniform(-0.5, 0.5)/bb
    ph = sum(p*cmath.exp(1j*tau*x) for p, x in zip(ps, xs))
    r = cmath.log(ph) + tau*tau*s2/2
    bound = 97/288*abs(tau)**3*bb*s2
    if bound > 0: worst = max(worst, abs(r)/bound)
P(" random test: max |r| / ((97/288)|tau|^3 b sigma^2) =", worst, " (<=1 required)")

P("== Core proposition constants ==")
G0 = (2*pi)**-0.5*exp(-mpf(1)/(2*10**4))
P(" (2pi)^(-1/2) e^{-1/(2V)} (V=1e4) =", G0, " >= 0.3988:", G0 >= mpf('0.3988'))
ta = 1/(50*pi); tb = 1/(200*pi**2); tc = 4/(100*pi); td = 4/pi*mpf('1e-3'); te = 2*mpf('1e-3')
P(" (a)", ta, "(b)", tb, "(c)", tc, "(d)", td, "(e)", te, " sum =", ta+tb+tc+td+te)
P(" lower bound G0 - sum =", G0-(ta+tb+tc+td+te), " >= 0.375:", G0-(ta+tb+tc+td+te) >= mpf('0.375'))
# check (a): Gaussian tail with tau1 sqrt V >= 50
P(" int_R |tau|^3 e^{-tau^2 V/4} dtau * V^2 = ", quad(lambda t: abs(t)**3*exp(-t**2/4), [-inf, inf]), "(=16)")
P(" int_R e^{-2 tau^2/pi^2} dtau =", quad(lambda t: exp(-2*t**2/pi**2), [-inf, inf]), " = pi^1.5/sqrt2 =", pi**1.5/sqrt(2))
s4 = pi**1.5/sqrt(2) + mpf('0.008') + 4*pi*mpf('1e-3')
Bc = pi/8*s4
P(" step4 sum =", s4, " B*T*sqrtV <=", Bc, " (claimed 1.555)")
tail = 2*mpf('1.555')/pi**2*(pi**2/6-1)
P(" step5 tail =", tail, " (claimed <=0.2033); pi^2/6-1 =", pi**2/6-1)
P(" step6 margin =", mpf('0.375')-tail)
# F_T lower bound on |x|<=1/(2T): sin v/v >= 2/pi on |v|<=pi/2
P(" 4/pi^2 =", 4/pi**2, " F_T identity check at T=3,x=0.123:",
  quad(lambda xi: (1-abs(xi)/3)*cos(2*pi*xi*mpf('0.123')), [-3, 3]), 3*(sin(pi*3*mpf('0.123'))/(pi*3*mpf('0.123')))**2)

P("== (C2) at n=n0 ==")
for LL in [6, 8, 10, 20, 50]:   # loglog y
    K = 32/c2*LL
    lhs = c2*K/4; rhs = log(1000) + 0.5*log(K) + 2*LL
    P(" loglog y = %d: lhs=8 loglog y=%s rhs=%s ok=%s" % (LL, lhs, rhs, lhs >= rhs))

P("== Dirichlet: 4 K^M <= (8/eta)^M for M>=15 ==")
bad = []
for M in range(10, 40):
    ok = True
    for k in range(1, 20001):
        eta = mpf(k)/20000
        K = int(math.floor(2*math.pi/float(eta))) + 1
        if 4*mpf(K)**M > (8/eta)**M: ok = False; break
    bad.append((M, ok))
P(" (M, holds for all eta in grid):", bad)
P(" K' check: eta=1: K'=", int(math.floor(math.pi*math.sqrt(2)))+1, " 2pi^2/K'^2 =", 2*math.pi**2/(int(math.floor(math.pi*math.sqrt(2)))+1)**2)

P("== Regime (c) harmonic bound ==")
for Lv in [1e3, 1e6, 1e12, 1e30]:
    K = int(math.log2(Lv)); s = sum(1/(1+k*math.log(2)) for k in range(0, K+1))
    P(" L=%g: sum=%.4f bound=%.4f" % (Lv, s, 1+math.log(1+math.log(Lv))/math.log(2)))

P("== Small zone (iii) constant: 2*sum 2^{j/2} <= 7 sqrt(l1)?  2/(1-2^-1/2) =", 2/(1-2**-0.5))

open(__file__.replace('code/aud3_vkgap_constants.py', 'out/aud3_vkgap_constants.txt'), 'w').write("\n".join(out)+"\n")
