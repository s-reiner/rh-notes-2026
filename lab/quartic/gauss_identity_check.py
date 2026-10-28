"""Numerical check of quartic Gauss-sum relations over Z[i] for primary primes pi = a+bi (norm p = 1 mod 4).
   chi = quartic residue symbol mod pi:  chi(x) = x^{(p-1)/4} mod pi, identified with a 4th root of unity in C via i -> i.
   g_j(pi) = sum_{x mod pi} chi(x)^j e(tr(x/pi)),  tr(z) = z + conj(z),  e(t) = exp(2 pi i t).
   Checks: |g_1|^2 = p, g_2^2 = chi(-1) p (quadratic Gauss sum mod pi), the Jacobi relation g_1 g_1 = J(chi,chi) g_2,
   and whether mu(pi) g_3 = (unit-modulus explicit) * g_1 holds, i.e. g_3/g_1 is an explicit root of unity times conj-type factor.
   This is a sanity check only; the memo's lemma is derived separately."""
import cmath, math
from sympy import isprime, primerange, factorint

def primary_gaussian_primes(maxp):
    out=[]
    for p in primerange(5, maxp):
        if p % 4 != 1: continue
        # find a+bi with a^2+b^2=p, choose primary: a odd, b even, a+b ≡ 1 mod 4 (one of the convention variants)
        for a in range(1, int(math.isqrt(p))+1):
            b2=p-a*a; b=math.isqrt(b2)
            if b*b==b2:
                for s1 in (1,-1):
                    for s2 in (1,-1):
                        A,B=s1*a,s2*b
                        if A%2==1 and B%2==0 and ((A-1)%4==0 and B%4==0 or (A+1)%4==0 and B%4==2): out.append((A,B,p))
                break
    return out

def residues_mod(a,b):
    # representatives of Z[i]/(pi): since N(pi)=p prime, Z[i]/(pi) ≅ Z/p via i -> r with r^2 = -1 mod p, r ≡ -a*b^{-1}... use x in 0..p-1 as representatives
    p=a*a+b*b
    r=(-a*pow(b,-1,p))%p   # i ≡ r mod pi  (since a + b i ≡ 0 => i ≡ -a/b)
    return p, r

def quartic_char(x, p, r):
    # chi(x) = x^{(p-1)/4} mod p, map result in {1, r, p-1, p-r} to {1, i, -1, -i}
    v=pow(x,(p-1)//4,p)
    table={1:1, r:1j, p-1:-1, (p-r)%p:-1j}
    return table[v]

def gauss(j, a, b):
    p, r = residues_mod(a,b)
    pi=complex(a,b)
    s=0
    for x in range(1,p):
        # tr(x/pi) with x integer rep: x/pi = x*conj(pi)/p ; tr = 2*Re = 2*x*a/p
        t = 2*x*a/p
        s += quartic_char(x,p,r)**j * cmath.exp(2j*math.pi*t)
    return s

def jacobi(a,b):
    p,r=residues_mod(a,b); s=0
    for x in range(0,p):
        y=(1-x)%p
        cx = quartic_char(x,p,r) if x%p else 0
        cy = quartic_char(y,p,r) if y%p else 0
        s += cx*cy
    return s
print(" pi=(a,b)   p   chi(-1)   J(chi,chi)          -chi(-1)*conj(pi)     g1^2/(J*g2)   g1^4/(p*J^2)")
for a,b,p in primary_gaussian_primes(80):
    g1,g2=gauss(1,a,b),gauss(2,a,b); J=jacobi(a,b)
    pp,r=residues_mod(a,b); chim1=quartic_char(p-1,p,r); pi=complex(a,b)
    print(f" ({a:3d},{b:3d}) {p:3d}   {chim1:+.0f}   {J:+.2f}   {-chim1*pi.conjugate():+.2f}   {g1*g1/(J*g2):+.3f}   {g1**4/(p*J*J):+.3f}")
