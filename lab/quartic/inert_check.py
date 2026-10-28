# Check Lemma 1 (i)-(iv) for squarefree primary n in Z[i] INCLUDING inert prime factors (-q, q = 3 mod 4).
# O/(n) sampled via the box [0,N)^2 (fundamental domain of N*O, each class of O/(n) hit N times).
import cmath, math, itertools
def primary(a,b): return (a%4==1 and b%4==0) or (a%4==3 and b%4==2)
def gi_mul(x,y,q):  # multiply in F_q[i]
    return ((x[0]*y[0]-x[1]*y[1])%q, (x[0]*y[1]+x[1]*y[0])%q)
def gi_pow(x,e,q):
    r=(1,0)
    while e:
        if e&1: r=gi_mul(r,x,q)
        x=gi_mul(x,x,q); e>>=1
    return r
def chi_inert(x,q):  # pi=-q, N=q^2, x=(a,b) in F_q[i]; chi = x^{(q^2-1)/4} in {1,i,-1,-i}
    a,b=x[0]%q,x[1]%q
    if a==0 and b==0: return 0
    v=gi_pow((a,b),(q*q-1)//4,q)
    return {(1,0):1,(0,1):1j,(q-1,0):-1,(0,q-1):-1j}[v]
def chi_split(x,a,b,p):
    r=(-a*pow(b,-1,p))%p
    t=(x[0]+x[1]*r)%p
    if t==0: return 0
    v=pow(t,(p-1)//4,p)
    return {1:1,r:1j,p-1:-1,(p-r)%p:-1j}[v]
def chi_n(x,facs):
    c=1
    for f in facs:
        c*= chi_inert(x,f[0]) if f[1]=='inert' else chi_split(x,*f[0])
    return c
def elem(facs):
    n=complex(1,0)
    for f in facs: n*= complex(-f[0],0) if f[1]=='inert' else complex(f[0][0],f[0][1])
    return n
def gauss(j,facs):
    n=elem(facs); N=round(abs(n)**2); a,b=round(n.real),round(n.imag)
    assert primary(a,b), (a,b)
    s=0
    for x in range(N):
        for y in range(N):
            c=chi_n((x,y),facs)
            if c==0: continue
            # Tr((x+iy)/n) = 2 Re((x+iy)*conj(n))/N = 2(x a + y b)/N
            s+= c**j*cmath.exp(2j*math.pi*((2*(x*a+y*b))%N)/N)
    return s/N/math.sqrt(N)
def check(facs):
    n=elem(facs); N=round(abs(n)**2); mu=(-1)**len(facs); al=n/abs(n)
    g1,g2,g3=(gauss(j,facs) for j in (1,2,3))
    chim1=chi_n((N-1,0),facs); eps=(-1)**((N-1)//4)
    e1=abs(g1*g1-mu*al); e2=abs(g2-chim1)+abs(chim1-eps); e3=abs(g1*g3-chim1); e4=abs(mu*g3-chim1*al.conjugate()*g1)
    print(f"n={n.real:+.0f}{n.imag:+.0f}i N={N:5d} mu={mu:+d} g1={g1:+.3f} g2={g2:+.3f} chi(-1)={chim1:+.0f} errs (i)-(iv): {e1:.1e} {e2:.1e} {e3:.1e} {e4:.1e}")
I3=(3,'inert'); I7=(7,'inert'); I11=(11,'inert'); S5=((-1,2,5),"split"); S13=((3,2,13),"split"); S17=((1,4,17),"split")
for facs in [[I3],[I7],[I11],[I3,S5],[I7,S5],[I3,I7],[I3,S13],[I3,S5,S13]]:
    check(facs)
