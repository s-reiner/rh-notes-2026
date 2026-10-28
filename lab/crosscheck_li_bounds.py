"""
Cross-check for Experiment 1 (NOT part of the proof; floating/high-precision sanity only).

(1) Compute lambda_n directly (contour method, 50 digits) for n in a test set.
(2) Compute the Lemma-4 lower bound A_low(n) with the SAME formulas as the certifier,
    and check A_low(n) <= lambda_n. If A_low(n) > lambda_n for any n, the derivation is wrong
    (because B_n is tiny for these n, lambda_n ~ A_n).
(3) Compare lambda_n with the partial zero sum over the first K zeros (identity check).
"""
import mpmath as mp
import sys
sys.path.insert(0, 'lab')
from certify_li_threshold import A_low, E_star, J, T0
from flint import arb

mp.mp.dps = 50

def xi(s):
    if s == 1:
        return mp.mpf('0.5')
    return mp.mpf('0.5') * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)

def li_coeffs(N):
    coeffs = mp.taylor(lambda z: mp.log(xi(1 / (1 - z))), 0, N, method='quad', radius=mp.mpf('0.5'))
    return [mp.re(n * coeffs[n]) for n in range(1, N + 1)]

N = 60
lam = li_coeffs(N)
K = 2000
zeros = [mp.im(mp.zetazero(k)) for k in range(1, K + 1)]
print(f"lambda_n (direct), partial on-line zero sum over first {K} zeros, Lemma-4 lower bound A_low(n):")
ok = True
for n in (1, 2, 5, 10, 20, 30, 40, 50, 60):
    theta = [2 * mp.atan(1 / (2 * g)) for g in zeros]
    partial = sum(2 * (1 - mp.cos(n * t)) for t in theta)
    alow = A_low(n, n)
    flag = "" if float(alow.upper()) <= float(lam[n-1]) else "  <-- VIOLATION"
    if flag: ok = False
    print(f"n={n:3d}  lambda={mp.nstr(lam[n-1], 12):<16} partial_sum={mp.nstr(partial, 12):<16} A_low={alow.str(6):<14}{flag}")
print("A_low <= lambda_n for all tested n:", ok)


# (4) Scale-model falsification test of Lemma 4' with a small "verification height" T0s,
#     using actual zeros (mpmath, non-certified) with T0s replaced everywhere, and the
#     HSW bound R(t) which is valid for all t >= e.  If A'(n,T1) > actual sum for some n,
#     Lemma 4' is wrong.
print()
print("Scale-model test of Lemma 4' (T0s = 1000, zeros below 1000, n up to T0s^2):")
T0s = 1000
zs = []
k = 1
while True:
    g = mp.im(mp.zetazero(k))
    if g > T0s: break
    zs.append(g); k += 1
print(f"  zeros below {T0s}: {len(zs)}")
def Rf(t): return mp.mpf('0.1038')*mp.log(t) + mp.mpf('0.2573')*mp.log(mp.log(t)) + mp.mpf('9.3675')
def Mf(t): return t/(2*mp.pi)*mp.log(t/(2*mp.pi*mp.e))
def Mp(t): return mp.log(t/(2*mp.pi))/(2*mp.pi)
def Aprime(n, T0, T1):
    return 2*(Mf(T0)-Mf(T1)-2*Rf(T0)-2*Rf(T1)) - 4*Mp(T0)*(T0**2+mp.mpf(1)/4)/n - 2*n*Rf(T0)*(1/T1-1/T0)
viol = 0
import random
random.seed(1)
tests = [int(10**e) for e in [2,3,4,5,5.5,6]] + [random.randint(1000, 10**6) for _ in range(40)]
for T1 in (T0s/2, T0s/4):
    worst = None
    for n in tests:
        actual = sum(2*(1-mp.cos(n*2*mp.atan(1/(2*g)))) for g in zs if g > T1)
        bound = Aprime(n, T0s, T1)
        if bound > actual: viol += 1; print(f"  VIOLATION n={n} T1={T1}: bound {bound} > actual {actual}")
        slack = actual - bound
        if worst is None or slack < worst[0]: worst = (slack, n, actual, bound)
    print(f"  T1={T1}: min slack over {len(tests)} n = {mp.nstr(worst[0],6)} at n={worst[1]} (actual={mp.nstr(worst[2],6)}, bound={mp.nstr(worst[3],6)})")
print("  violations:", viol)
