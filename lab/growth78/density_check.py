"""Check: does the improved mu(alpha) (Cor. 2) give anything via Montgomery Thm 12.3 (ANTEDB Lemma 11.27)
   A(sigma) <= mu(alpha) * 2(3 sigma - 1 - 2 alpha)/((2 sigma - 1 - alpha)(sigma - alpha)),  (alpha+1)/2 <= sigma <= 1,
   on [0.842, 7/8)?  Compare with Huxley 3/(3 sigma - 1) and ANTEDB Table 11.1 value 3/(2 sigma) there."""
from fractions import Fraction as F
import numpy as np
from compare_mu import pieces  # noqa
def table(s):
    for a,b,lo,hi in pieces:
        if lo<=s<=hi: return a-b*s
    return None
def mu_new(a):
    if a>=F(7,8): return F(0)
    t=table(a); c=F(26,63)*(F(7,8)-a)
    return min(t,c) if t is not None else c
for sig in [F(85,100),F(86,100),F(87,100),F(7,8)]:
    best=None
    for k in range(1,2000):
        al=F(1,2)+ (2*sig-1-F(1,2))*F(k,2000)   # alpha in [1/2, 2 sigma - 1)
        if al>=2*sig-1 or al>=sig: continue
        m=mu_new(al)
        if m==0: continue
        A=m*2*(3*sig-1-2*al)/((2*sig-1-al)*(sig-al))
        if best is None or A<best[0]: best=(A,al)
    print(f"sigma={float(sig):.3f}: min over alpha of Lemma 11.27 bound = {float(best[0]):.3f} at alpha={float(best[1]):.4f};  Huxley 3/(3s-1)={float(3/(3*sig-1)):.3f}; Table 11.1 3/(2s)={float(3/(2*sig)):.3f}")
