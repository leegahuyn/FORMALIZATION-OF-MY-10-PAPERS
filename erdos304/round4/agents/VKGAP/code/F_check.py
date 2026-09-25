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
# (c) h(t)=(1-sqrt(g))/t^2 >= 0.0194 on [0.02,1] (interval), and near 0 via bound 1-|F|>=(1-a)t^2/(2(1+t^2)), a=2log^2 2
ok=True; N=4000; mn=mpf(10)
for k in range(N):
    a=0.02+mpf(k)*0.98/N; b=0.02+mpf(k+1)*0.98/N
    I=iv.mpf([a,b]); v=(1-iv.sqrt(g(I)))/(I*I)
    mn=min(mn,v.a)
    if not (v.a>=0.0194): ok=False
print("(c) min lower bound of (1-|F|)/t^2 on [0.02,1] =",mn," >=0.0194:",ok)
a2=2*log(2)**2
print("analytic: a=2log^2 2=",a2," sup_{|t|>=1}|F| <= sqrt((1+a)/2)=",sqrt((1+a2)/2),"; (1-a)/(2*(1+0.02^2))=",(1-a2)/(2*(1+mpf('0.0004'))))
