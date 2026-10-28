from fractions import Fraction as F
import math, os
D=24
def dn(x): return F(math.floor(x*10**D),10**D)
def up(x): return F(math.ceil(x*10**D),10**D)
def s(x):  # decimal string of a Fraction with denominator 10^D
    neg=x<0; x=abs(x); i=x.numerator*10**D//x.denominator
    st=str(i).rjust(D+1,'0'); r=st[:-D]+'.'+st[-D:]; return ('-' if neg else '')+r
def logser(r,n):
    x=1-r; S=sum(x**(i+1)/(i+1) for i in range(n)); e=abs(x)**(n+1)/(1-abs(x)); return (-S-e,-S+e)
W=F(1,10**18)  # slack
lo,hi=logser(F(1,2),50); L2=(dn(-hi-W),up(-lo+W))
lo,hi=logser(F(3,4),25); L3=(dn(lo+2*L2[0]-W),up(hi+2*L2[1]+W))
lo,hi=logser(F(5,4),25); L5=(dn(lo+2*L2[0]-W),up(hi+2*L2[1]+W))
Pm=F('3.14159265358979323846'); Pp=F('3.14159265358979323847')
a=logser(Pm*8/25,8)[0]; b=logser(Pp*8/25,8)[1]
LP=(dn(a-3*L2[1]+2*L5[0]-W), up(b-3*L2[0]+2*L5[1]+W))
lT0=(L3[0]+12*L2[0]+12*L5[0], L3[1]+12*L2[1]+12*L5[1])
lT1=(13*L2[0]+12*L5[0], 13*L2[1]+12*L5[1])
# anchors for loglog: rationals r0lo<=lT0*5/144 etc
r0=(dn(lT0[0]*5/144),up(lT0[1]*5/144)); r1=(dn(lT1[0]*8/225),up(lT1[1]*8/225))
x=logser(r0[0],8)[0]; y=logser(r0[1],8)[1]
LL0=(dn(x+4*L2[0]+2*L3[0]-L5[1]-W), up(y+4*L2[1]+2*L3[1]-L5[0]+W))
x=logser(r1[0],8)[0]; y=logser(r1[1],8)[1]
LL1=(dn(x+2*L3[0]+2*L5[0]-3*L2[1]-W), up(y+2*L3[1]+2*L5[1]-3*L2[0]+W))
T0=F(3*10**12); T1=F(2*10**12); n1=1918555885591938922971136; n2=1918555899886294190260224
c=1+F(2)/T0**2
L0=(L3[0]+11*L2[0]+12*L5[0]-LP[1], L3[1]+11*L2[1]+12*L5[1]-LP[0])
L1=(12*L2[0]+12*L5[0]-LP[1], 12*L2[1]+12*L5[1]-LP[0])
Wm=dn(1/(2*Pp)); Wp=up(1/(2*Pm))
R0p=F('0.10076')*lT0[1]+F('0.24460')*LL0[1]+F('8.08344')
R1p=F('0.10076')*lT1[1]+F('0.24460')*LL1[1]+F('8.08344')
q=(T0**2+F(1,4))/n1
Bm=dn(2*T0*(L0[0]-1)-2*T1*(L1[1]-1)-4*L0[1]*q - W)
rhs=dn(Wm*Bm - 4*R0p - 4*R1p - 2*n2*R0p*(1/T1-1/T0) - F(1,10**6))
u=n2*c/(4*T0**2); U=F(math.ceil(u*10**30),10**30)
def expup(x,n=12): return sum(x**m/math.factorial(m) for m in range(n))+abs(x)**n*F(n+1,math.factorial(n)*n)
chp=up((expup(U)+expup(-U))/2)
Jp=(lambda v: F(math.ceil(v*10**66),10**66))(2*R0p/T0**4+(L0[1]/3+F(1,9))*Wp/T0**3+F('0.10076')/(4*T0**4)+F('0.24460')/(4*T0**4*lT0[0]))
E=F(n2)**2*c**2/4*chp**2*Jp
print('margin',float(rhs-E))
C=dict(L2lo=s(L2[0]),L2hi=s(L2[1]),L3lo=s(L3[0]),L3hi=s(L3[1]),L5lo=s(L5[0]),L5hi=s(L5[1]),
 LPlo=s(LP[0]),LPhi=s(LP[1]),LL0lo=s(LL0[0]),LL0hi=s(LL0[1]),LL1lo=s(LL1[0]),LL1hi=s(LL1[1]),
 r0lo=s(r0[0]),r0hi=s(r0[1]),r1lo=s(r1[0]),r1hi=s(r1[1]),Bm=s(Bm),rhs=s(rhs),U=str(U.numerator)+'/'+str(U.denominator),
 chp=s(chp),Jp=str(math.ceil(Jp*10**66))+'/10^66',n1=n1,n2=n2,Wm=s(Wm),Wp=s(Wp))
import json; json.dump(C,open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'consts.json'),'w'),indent=1); print(json.dumps(C,indent=1))
Jc=2*(F('0.10076')*F('28.73')+F('0.24460')*LL0[1]+F('8.08344'))/T0**4+((L3[1]+11*L2[1]+12*L5[1]-LP[0])/3+F(1,9))*Wp/T0**3+F('0.10076')/(4*T0**4)+F('0.24460')/(4*T0**4*F('28.729'))
Jp2=F(math.ceil(Jc*10**66)+1,10**66)
print('Jp2',math.ceil(Jc*10**66)+1)
E2=F(n2)**2*c**2/4*chp**2*Jp2
print('margin2',float(rhs-E2))
