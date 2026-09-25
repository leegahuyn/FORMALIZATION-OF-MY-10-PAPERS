# VKGAP numerics (2): F(tau)=(2-2^{-i tau})/(1+i tau); |F|^2=g(tau)=(5-4cos(tau log2))/(1+tau^2).
# Interval-arithmetic check (mpmath.iv) that sup_{|tau|>=1}|F| = |F(1)| and of 1-|F|>=0.0194 tau^2 on (0,1].
from mpmath import iv, mp, mpf, cos, sin, log, sqrt
mp.dps=30; iv.dps=30
def g(t): return (5-4*iv.cos(t*iv.log(2)))/(1+t*t)
def gp_num(t):  # numerator of g'(t)*(1+t^2)^2
    l=iv.log(2); return 4*l*iv.sin(t*l)*(1+t*t)-2*t*(5-4*iv.cos(t*l))
g1=(5-4*cos(log(2)))/2
print("g(1)=|F(1)|^2=",g1," |F(1)|=",sqrt(g1))
# (a) derivative negative on [1,1.05]
ok=True; N=500
for k in range(N):
    a=1+mpf(k)*0.05/N; b=1+mpf(k+1)*0.05/N
    v=gp_num(iv.mpf([a,b]))
    if not (v.b<0): ok=False; print("deriv not neg on",a,b,v)
print("(a) g'<0 on [1,1.05]:",ok)
# (b) g <= g(1)-margin on [1.05,3]; for tau>=3, g<=9/10<g(1)
ok=True; N=4000; mx=mpf(0)
for k in range(N):
    a=1.05+mpf(k)*1.95/N; b=1.05+mpf(k+1)*1.95/N
    v=g(iv.mpf([a,b]))
    mx=max(mx,v.b)
    if not (v.b<g1): ok=False; print("fail",a,b,v)
print("(b) max upper bound of g on [1.05,3] =",mx," < g(1):",ok, "; tau>=3: g<=9/10 =",0.9)
# (c) 1-|F(t)| >= 0.0194 t^2 on (0,1].  Write 1-|F|^2 = t^2 X(t)/(1+t^2), X(t)=1-2log^2(2) sinc^2(t log2/2),
# X increasing on [0,1] (sinc decreasing on [0,pi]); t^2/(1+t^2) increasing.  On [a,b]:
# 1-|F| = (1-|F|^2)/(1+|F|) >= t^2 X(a) / ((1+b^2)(1+fup)),  fup = sqrt(1 - a^2 X(a)/(1+a^2)) >= |F| on [a,b].
# Endpoint evaluations in 40-digit arithmetic; margins >> rounding.  On (0,0.08]: X>=X(0), 1+|F|<=2.
mp.dps=40
l2=log(2)
def X(t): 
    x=t*l2/2
    return 1-2*l2**2*(sin(x)/x)**2 if t>0 else 1-2*l2**2
b0=mpf('0.08'); lb0=X(0)/(2*(1+b0**2))
print("(c0) on (0,0.08]: (1-|F|)/t^2 >=",lb0," >=0.0194:",lb0>=mpf('0.0194'))
ok=True; mn=mpf(1); N=20000
for k in range(N):
    a=b0+(1-b0)*mpf(k)/N; b=b0+(1-b0)*mpf(k+1)/N
    Xa=X(a); fup=sqrt(1-a**2*Xa/(1+a**2))
    v=Xa/((1+b**2)*(1+fup)); mn=min(mn,v)
    if v<mpf('0.0194'): ok=False
print("(c1) on [0.08,1] (",N,"subintervals): min certified lower bound of (1-|F|)/t^2 =",mn," >=0.0194:",ok)
print("   exact 1-|F(1)| =",1-sqrt(g1),"(so the constant 0.0194 is sharp to 3e-5 at t=1)")
a2=2*log(2)**2
print("analytic: a=2log^2 2=",a2," sup_{|t|>=1}|F| <= sqrt((1+a)/2)=",sqrt((1+a2)/2))
