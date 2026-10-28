import sys; import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import certify_li_threshold as C
from flint import arb
T0=C.T0; c=arb(1)+2/T0**2; JT=C.J(T0)
n1=1; ratio=2.0; out=[]
names=['T0/2','T0/3','2T0/3','T0/4','T0/10']
while True:
    n2=max(n1+1,int(n1*ratio))
    best=C.A_low(n1,n2); kind='A1'
    for nm,T1 in zip(names,C.T1_CHOICES):
        cand=C.A_prime_low(n1,n2,T1)
        if cand>best: best=cand; kind='A2 '+nm
    rhs=C.E_star(n2,c,JT)
    if best-rhs>0:
        out.append((n1,n2,kind,best,rhs)); n1=n2
        if ratio<2.0: ratio=min(2.0,1+2*(ratio-1))
    else:
        if ratio-1<1e-9: break
        ratio=1+(ratio-1)/2
print(len(out), n1)
from collections import Counter
print(Counter(k for _,_,k,_,_ in out))
for (a,b,k,l,r) in out:
    rel=(l-r)/abs(l)
    print(a,b,k,l.str(8),r.str(8),rel.str(3))
