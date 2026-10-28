"""
Baseline reproduction: Li coefficients lambda_n for small n.

Question: do two independent computations of lambda_n agree with each other and
with the published closed form for lambda_1?

Method A (derivative form, Li 1997 / Bombieri-Lagarias 1999):
    lambda_n = (1/(n-1)!) d^n/ds^n [ s^(n-1) log xi(s) ]  at s = 1
Implemented via Taylor coefficients of  phi(z) = log xi(1/(1-z))  at z = 0:
    log xi(1/(1-z)) = sum_{n>=1} lambda_n z^n / n     (Li's generating function)
so lambda_n = n * [z^n] phi(z).

Method B (closed form for lambda_1, Bombieri-Lagarias):
    lambda_1 = 1 + gamma/2 - (1/2) log(4 pi)

Precision: mpmath with 60 decimal digits; Taylor coefficients by mpmath.taylor
(numerical differentiation of an analytic function). Truncation/rounding error
is estimated by recomputing at 80 digits and reporting the discrepancy.

This script proves nothing about RH. It checks that the laboratory reproduces
known numbers.
"""
import mpmath as mp

def xi(s):
    if s == 1:
        return mp.mpf('0.5')          # (s-1)zeta(s) -> 1 as s -> 1
    return mp.mpf('0.5') * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)

def log_xi_z(z):
    s = 1 / (1 - z)
    return mp.log(xi(s))

def li_coeffs(N, dps):
    mp.mp.dps = dps
    # Taylor coefficients by Cauchy integral on |z| = 1/2.  Under s = 1/(1-z)
    # this circle maps to |s - 4/3| = 2/3, i.e. Re s in [2/3, 2], |Im s| <= 2/3.
    # xi has no zeros there unconditionally: the lowest zero has |Im rho| ~ 14.13
    # (and RH is verified numerically to height 3e12, Platt-Trudgian 2021), so
    # log xi(1/(1-z)) is analytic on |z| <= 1/2 and the contour integral is
    # legitimate without assuming RH.
    coeffs = mp.taylor(log_xi_z, 0, N, method='quad', radius=mp.mpf('0.5'))
    return [n * coeffs[n] for n in range(1, N + 1)]

if __name__ == "__main__":
    N = 12
    a = li_coeffs(N, 60)
    b = li_coeffs(N, 80)
    mp.mp.dps = 30
    closed = 1 + mp.euler / 2 - mp.log(4 * mp.pi) / 2
    print(f"lambda_1 closed form   = {mp.nstr(closed, 25)}")
    print(f"lambda_1 derivative    = {mp.nstr(a[0], 25)}")
    print(f"|difference|           = {mp.nstr(abs(a[0]-closed), 5)}")
    print()
    print(" n   lambda_n (60 dps)            |60dps - 80dps|")
    for n in range(1, N + 1):
        print(f"{n:2d}   {mp.nstr(a[n-1], 20):<26} {mp.nstr(abs(a[n-1]-b[n-1]), 3)}")
