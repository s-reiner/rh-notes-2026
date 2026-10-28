"""
Certified positivity threshold for Li coefficients (Experiment 1).

Implements the Theorem of reports/01-experiment1-derivation.md in ball arithmetic
(Arb via python-flint). A comparison counts as certified only when the arb
comparison returns True, which Arb guarantees only if the balls are disjoint.

Inputs (see derivation for citations):
  T0 = 3e12         Platt-Trudgian verification height
  R(T) = 0.1038 log T + 0.2573 log log T + 9.3675   (HSW 2022, T >= e)
  c_beta = 1 (unconditional)
Output: largest N0 reached by a chain of certified intervals [n1, n2] starting at n1 = 1.
"""
import sys
from flint import arb, ctx

ctx.dps = 60

PI = arb.pi()
T0 = arb(3) * arb(10) ** 12

def R(t):                      # HSW explicit error term, t >= e
    return arb("0.1038") * t.log() + arb("0.2573") * t.log().log() + arb("9.3675")

def M(t):                      # main term (t/2pi) log(t/(2 pi e))
    return t / (2 * PI) * (t / (2 * PI * arb(1).exp())).log()

def J(T):                      # tail constant, Lemma 3
    return (2 * R(T) / T ** 4
            + ((T / (2 * PI)).log() / 3 + arb(1) / 9) / (2 * PI * T ** 3)
            + arb("0.1038") / (4 * T ** 4)
            + arb("0.2573") / (4 * T ** 4 * T.log()))

def E_star(n, c, JT):          # upper bound for the tail loss, Lemma 3
    n = arb(n)
    u0 = n * c / (4 * T0 ** 2)
    return (n ** 2 * c ** 2 / 4) * u0.cosh() ** 2 * JT

def int_R_t3(a, b):            # UPPER bound for int_a^b R(t) t^-3 dt, using loglog t <= log t
    def F(t):                  # antiderivative of (0.1038+0.2573) log t / t^3 + 9.3675 / t^3
        return -(arb("0.1038") + arb("0.2573")) * (2 * t.log() + 1) / (4 * t ** 2) - arb("9.3675") / (2 * t ** 2)
    return F(b) - F(a)

def S_minus(a):                # lower bound for sum_{a<gamma<=T0} gamma^-2, Lemma 4
    return ((M(T0) - R(T0)) / T0 ** 2
            - (M(a) + R(a)) / a ** 2
            + ((a / (2 * PI)).log() / a - (T0 / (2 * PI)).log() / T0) / PI
            - 2 * int_R_t3(a, T0))

def A_low(n1, n2):             # lower bound for A_n on integers n1 <= n <= n2, Lemma 4
    a = arb(n2) / PI
    if a < arb(60):
        a = arb(60)
    if not (a <= T0):          # Lemma 4 requires a <= T0; outside its domain return a useless bound
        return arb(-1)
    return (4 * arb(n1) ** 2 / PI ** 2) * (1 - 1 / (12 * a ** 2)) ** 2 * S_minus(a)

def Mprime(t):
    return (t / (2 * PI)).log() / (2 * PI)

def A_prime_low(n1, n2, T1):   # Lemma 4', valid for all integers n in [n1, n2]
    return (2 * (M(T0) - M(T1) - 2 * R(T0) - 2 * R(T1))
            - 4 * Mprime(T0) * (T0 ** 2 + arb(1) / 4) / arb(n1)
            - 2 * arb(n2) * R(T0) * (1 / T1 - 1 / T0))

T1_CHOICES = [T0 / 2, T0 / 3, T0 * 2 / 3, T0 / 4, T0 / 10]

def head_low(n1, n2):
    best = A_low(n1, n2)
    for T1 in T1_CHOICES:
        cand = A_prime_low(n1, n2, T1)
        if cand > best:
            best = cand
    return best

def certify(c_beta):
    c = arb(c_beta) + 1 / T0 ** 2
    JT = J(T0)
    n1 = 1
    ratio = 2.0
    n_intervals = 0
    last_ok = None
    while True:
        n2 = max(n1 + 1, int(n1 * ratio))
        lhs = head_low(n1, n2)
        rhs = E_star(n2, c, JT)
        if (lhs - rhs) > 0:        # certified only if balls are disjoint
            n_intervals += 1
            last_ok = (n1, n2, lhs, rhs)
            n1 = n2                 # intervals overlap at the endpoint: fine
            if ratio < 2.0:
                ratio = min(2.0, 1 + 2 * (ratio - 1))
        else:
            if ratio - 1 < 1e-9:
                break
            ratio = 1 + (ratio - 1) / 2
    return n1, n_intervals, last_ok

if __name__ == "__main__":
    print(f"T0 = {T0}   J(T0) = {J(T0)}")
    print(f"S_minus(60) = {S_minus(arb(60))}   (must be > 0)")
    for c_beta in ("1",):
        cb = arb(1)
        N0, k, last = certify(cb)
        print(f"\nc_beta = {c_beta}:  certified  lambda_n > 0  for all  1 <= n <= N0 = {N0}  ({N0:.3e})  using {k} intervals")
        print(f"   last certified interval [{last[0]}, {last[1]}]: head_low = {last[2].str(12)}  E* = {last[3].str(12)}")
    # sanity: show the two sides at a few n
    JT = J(T0); c = arb(1) + 1 / T0 ** 2
    for n in (1, 10, 10**3, 10**6, 10**12, 10**13, 10**14, 10**20, 10**23, 5*10**23, 10**24, 10**25):
        print(f"n={n:.0e}: A_low={A_low(n, n).str(5)}  A'_low(T1=T0/2)={A_prime_low(n, n, T0/2).str(5)}  E*={E_star(n, c, JT).str(5)}")
