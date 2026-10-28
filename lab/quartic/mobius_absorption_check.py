"""Moebius-absorption lemma for quartic Gauss sums over Z[i] (quartic analogue of OpenAI Lemma 4.1 / (4.5)).

Conventions.  K = Q(i), O = Z[i].  n in O is PRIMARY if n = 1 mod (2+2i)  (a = 1 mod 4, b = 0 mod 4  or  a = 3 mod 4, b = 2 mod 4).
Quartic symbol: for a primary prime pi of norm p, chi_pi(x) = the 4th root of unity in O with chi_pi(x) = x^{(p-1)/4} (mod pi);
extended multiplicatively in the denominator to squarefree primary n.  Additive character e(z) = exp(2 pi i Tr(z)), Tr(z) = z + conj(z).
Normalised Gauss sums  gt_j(n) = N(n)^{-1/2} sum_{x mod n} chi_n(x)^j e(x/n),  j = 1,2,3 (= -1).
alpha(n) = n/|n|.   mu = Moebius.   eps(n) := chi_n(-1) = (-1)^{(N n - 1)/4}  (ray class character mod 4).

Claimed lemma (prime level, to be checked):   gt_1(pi)^2 = -alpha(pi),   gt_2(pi) = chi_pi(-1) = (-1)^{(p-1)/4},
    hence   mu(pi) * gt_{-1}(pi) = chi_pi(-1) * conj(alpha(pi)) * gt_1(pi).
Squarefree level (CRT + quartic reciprocity):   mu(n) * gt_{-1}(n) = chi_n(-1) * conj(alpha(n)) * gt_1(n).
Representatives: for n = a+bi with gcd(a,b)=1, O/(n) = Z/N(n) with i -> -a b^{-1}; for a prime factor pi_j the residue of an integer x
mod pi_j is x mod p_j.   e(x/n) = exp(2 pi i * 2 a x / N(n)) for an integer representative x.
"""
import cmath, math, itertools
from sympy import primerange

def primary_primes(maxp):
    out = []
    for p in primerange(5, maxp):
        if p % 4 != 1: continue
        for a in range(1, math.isqrt(p) + 1):
            b = math.isqrt(p - a*a)
            if b*b == p - a*a:
                for A, B in ((a,b),(-a,b),(a,-b),(-a,-b),(b,a),(-b,a),(b,-a),(-b,-a)):
                    if (A % 4 == 1 and B % 4 == 0) or (A % 4 == 3 and B % 4 == 2):
                        out.append((A, B, p))
                break
    return out

def chi_prime(x, a, b, p):
    """quartic symbol (x/pi)_4 for an integer x, pi = a+bi primary of norm p."""
    x %= p
    if x == 0: return 0
    r = (-a * pow(b, -1, p)) % p          # i = r (mod pi)
    v = pow(x, (p-1)//4, p)
    return {1: 1, r: 1j, p-1: -1, (p-r) % p: -1j}[v]

def chi_n(x, facs):
    c = 1
    for (a,b,p) in facs: c *= chi_prime(x, a, b, p)
    return c

def gauss(j, n, facs):
    a, b = int(n.real), int(n.imag); N = a*a + b*b
    assert math.gcd(a, b) == 1
    s = sum(chi_n(x, facs)**j * cmath.exp(2j*math.pi * (2*a*x % N) / N) for x in range(N))
    return s / math.sqrt(N)

def check(facs):
    n = complex(1, 0)
    for (a,b,p) in facs: n *= complex(a, b)
    N = round(abs(n)**2); mu = (-1)**len(facs); alpha = n/abs(n)
    g1, g2, g3 = (gauss(j, n, facs) for j in (1,2,3))
    chim1 = chi_n(N-1, facs)                       # chi_n(-1)
    eps = (-1)**((N-1)//4)
    lhs = mu * g3
    rhs = chim1 * alpha.conjugate() * g1
    return dict(n=n, N=N, g1sq_over_minus_alpha=g1*g1/(-alpha), g2=g2, chim1=chim1, eps=eps,
                g1g3=g1*g3, lhs=lhs, rhs=rhs, err=abs(lhs-rhs))

primes = primary_primes(80)
primes = [q for q in primes if q[1] > 0]   # one of each conjugate pair
print("PRIME LEVEL  (pi primary, p = N(pi))")
print(f"{'pi':>10} {'p':>3} {'gt1^2/(-alpha)':>16} {'gt2':>8} {'chi(-1)':>8} {'(-1)^((p-1)/4)':>15} {'gt1*gt3':>10} {'|mu gt3 - chi(-1) conj(alpha) gt1|':>36}")
for (a,b,p) in primes:
    r = check([(a,b,p)])
    print(f"{a:+4d}{b:+4d}i {p:3d} {r['g1sq_over_minus_alpha']:+.6f} {r['g2']:+.3f} {r['chim1']:+.0f} {r['eps']:+15d} {r['g1g3']:+.3f} {r['err']:36.2e}")

print("\nSQUAREFREE COMPOSITE LEVEL  n = pi1*pi2 (and one triple product), gcd(Re n, Im n) = 1")
combos = [c for c in itertools.combinations(primes[:6], 2)] + [c for c in itertools.combinations(primes[:5], 3)]
for facs in combos:
    n = complex(1,0)
    for (a,b,p) in facs: n *= complex(a,b)
    if math.gcd(int(round(n.real)), int(round(n.imag))) != 1: continue
    facs = [(a,b,p) for (a,b,p) in facs]
    r = check(facs)
    print(f"n={int(round(n.real)):+5d}{int(round(n.imag)):+5d}i  N={r['N']:6d}  mu={(-1)**len(facs):+d}  chi_n(-1)={r['chim1']:+.0f}  eps={r['eps']:+d}  gt2={r['g2']:+.3f}  "
          f"gt1^2/(-alpha)={r['g1sq_over_minus_alpha']:+.4f}  |LHS-RHS|={r['err']:.2e}")
