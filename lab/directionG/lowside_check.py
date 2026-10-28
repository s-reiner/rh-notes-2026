from fractions import Fraction as Fr
b,h,l=Fr(1,8),Fr(13,16),Fr(1,6)
lx=1+l-h; ly=lx+b; M=lx+ly
print("lx,ly,M,M+l:",lx,ly,M,M+l)
c=lx/2-1+h/6; print("C(s)=s+",c, " C(7/8)=",Fr(7,8)+c, " lx/2+b/12=",lx/2+b/12)
print("b from M+l=1:",2*h-3*l-1)
print("sigma0=1-h/6+b/12:",1-h/6+b/12," 11/12-l/4:",Fr(11,12)-l/4)
# Part I
lxI=lyI=hI=Fr(1,2); lI=0
print("PartI: h=1-lx+l:",1-lxI+lI," C=s+",lxI/2-1+hI/6," C(11/12)=",Fr(11,12)+lxI/2-1+hI/6, " sigma0=1-h/6:",1-hI/6)
# Lemma 15.1 second branch: 1+3l'-2M' = 1+3l-2M+d ; at d=l: 1+4l-2M
print("1+4l-2M:",1+4*l-2*M, " M-2l:",M-2*l)
# (15.7)-(15.8) checks
print("ly-l-11b/6:",ly-l-11*b/6, " lx-l:",lx-l, " ly-l:",ly-l)
# (20.4) check
z0=Fr(17,50)
def E(d,R,q,delta):
    a=(1+delta)/2
    return a-Fr(7,8)+h*(z0-Fr(1,6))-a*ly-(1-a)*l-(delta/2-q)*l+d*(R+delta/2-z0)
def E2(d,R,q,delta):
    C0=Fr(-1,48)
    return C0+Fr(2,3)*delta+q/6-h*(1-R)+(d-h)*(R+delta/2-z0)
import itertools
ok=all(E(d,R,q,dl)==E2(d,R,q,dl) for d in [Fr(1,2),h,1] for R in [Fr(1,3),1] for q in [0,Fr(1,5)] for dl in [Fr(1,50),Fr(5,6)])
print("(20.4) two lines agree:",ok)
print("(20.5) floor:",E2(h,1,Fr(1,100),Fr(1,50)), " (20.7) at delta=5/6:",E2(h,Fr(1,6),Fr(5,12),Fr(5,6)), -Fr(1,48)-Fr(5,6)/16)
print("(20.6):",h*(z0-Fr(1,6))-ly/2, " B0:",lx/2+1+ly, " 5l-h:",5*l-h, " l/h:",l/h, " 37/18 etc", Fr(8,39)-Fr(7,37))
# general sigma0 along 2M=1+4l with lx=1+l-h: ly=h+l-1/2
for hh in [Fr(3,4),Fr(13,16),Fr(5,6)]:
  for ll in [Fr(1,10),Fr(1,6)]:
    lxx=1+ll-hh; lyy=hh+ll-Fr(1,2); bb=lyy-lxx
    print(" h,l=",hh,ll," ly=",lyy," b=",bb," sigma0=",1-hh/6+max(bb,0)/12, " M+l=",lxx+lyy+ll)
print("---diffs E-E2---")
for d in [Fr(1,2),h,1]:
  for R in [Fr(1,3),1]:
    for q in [0,Fr(1,5)]:
      for dl in [Fr(1,50),Fr(5,6)]:
        print(d,R,q,dl, E(d,R,q,dl)-E2(d,R,q,dl))
# try with C0 from text: C0 maybe = a-7/8 ... recompute constant of E at d=h,R=0,q=0,delta=0
print("E(h,0,0,0)=",E(h,0,0,0), " E2(h,0,0,0)=",E2(h,0,0,0))
print("E(h,1,0,0)=",E(h,1,0,0), " E2(h,1,0,0)=",E2(h,1,0,0))
