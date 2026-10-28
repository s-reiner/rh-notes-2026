"""Cor. 8.13 (ANTEDB): LV(sigma,tau) <= max(2-2sigma, 2-2sigma+tau-(2sigma-1-sigma')/mu(sigma')).
Montgomery's conjecture range: tau <= T(sigma) := sup_{sigma' < 2sigma-1} (2sigma-1-sigma')/mu(sigma').
Compare T(sigma) with the ANTEDB Table 6.2 mu (old) vs min(table, (26/63)(7/8-sigma')) (new), for sigma in [0.78, 0.875]."""
from fractions import Fraction as F
from compare_mu import pieces
def table(s):
    for a,b,lo,hi in pieces:
        if lo<=s<=hi: return a-b*s
    return None
def mu_old(s): 
    t=table(s); return t
def mu_new(s):
    t=table(s); c=F(26,63)*(F(7,8)-s)
    return min(t,c) if t is not None else c
def T(sig, mu):
    best=F(0); arg=None
    lim=2*sig-1
    n=4000
    for k in range(0,n):
        sp=F(1,2)+(lim-F(1,2))*F(k,n)
        if sp>=lim: break
        m=mu(sp)
        if m is None or m<=0: continue
        v=(lim-sp)/m
        if v>best: best=v; arg=sp
    return best,arg
print(" sigma   T_old   T_new   gain   argmax_old argmax_new")
for sig in [F(78,100),F(80,100),F(82,100),F(84,100),F(85,100),F(86,100),F(87,100),F(7,8)]:
    to,ao=T(sig,mu_old); tn,an=T(sig,mu_new)
    print(f" {float(sig):.3f}  {float(to):.4f}  {float(tn):.4f}  {float(tn/to):.4f}   {float(ao):.3f}      {float(an):.3f}")
