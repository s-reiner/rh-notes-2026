import sympy as sp, numpy as np
from scipy.optimize import linprog
d, x, M, l, h, B, rho, al, cM, cP, kap = sp.symbols('delta x M ell h B rho alpha c_M c_P kappa', real=True)
d0 = sp.Rational(1, 50)
# ---- (a) exact floor barrier: min B s.t. B>=L0, B>=LK, B>=Floor, h>=1-M/2+l, h>=1+2l-M
L0 = sp.Rational(5, 6) + M/12 - l/6; LK = sp.Rational(1, 3) + 7*M/12 + l/3
Floor = 1 + d0 - (1 + d0)*M/2 + d0*l + h/3            # floor class delta0=1/50, x=1/2, R=1 (no witness)
hmin = 1 - M/2 + l
Fl = Floor.subs(h, hmin)
sol = sp.solve([sp.Eq(L0, LK), sp.Eq(L0, Fl)], [M, l])
print("exact LP vertex (L0=LK=Floor, b=0):", sol, " B =", L0.subs(sol), "=", float(L0.subs(sol)))
# with general floor delta0 -> general formula
dl = sp.symbols('delta_0')
Flg = (1 + dl - (1 + dl)*M/2 + dl*l + hmin/3)
solg = sp.solve([sp.Eq(L0, LK), sp.Eq(L0, Flg)], [M, l])
print("general delta0: l_max =", sp.simplify(solg[l]), " B_min =", sp.simplify(L0.subs(solg)), " at delta0->0:", sp.simplify(L0.subs(solg).subs(dl, 0)))
# ---- saturation rho: bisection with the same LP as before (coarse grid)
alpha = sp.Rational(5, 6)
Dx = 3 - sp.Rational(17, 9)*x; Px = (2 - sp.Rational(8, 9)*x)*(1 - x); J = (alpha - d)*Dx + d*Px
Rstar = 1 - d + (alpha - d)*d*Px/(2*J)
Rnum = sp.lambdify((d, x), Rstar, 'numpy')
dg = np.linspace(1/50 + 1e-9, 5/6, 400); xg = np.linspace(0, 0.5, 11)
DG, XG = np.meshgrid(dg, xg, indexing='ij'); RG = Rnum(DG, XG)
def Bmin(r):
    A = [[-1, 1/12, -1/6, 0], [-1, 7/12, 1/3, 0]]; bv = [-5/6, -1/3]
    for Dv, Xv, Rv in zip(DG.ravel(), XG.ravel(), RG.ravel()):
        A.append([-1, -(1 + Dv)/2, Dv*(0.5 + Xv), Rv - r - 2/3]); bv.append(-(1 + Dv))
    A.append([-1, -(1 + 1/50)/2, 1/50, 1/3]); bv.append(-(1 + 1/50))
    A += [[0, -1/2, 1, -1], [0, -1, 2, -1], [0, 0, 0, 1]]; bv += [-1, -1, 1]
    return linprog([1, 0, 0, 0], A_ub=np.array(A), b_ub=np.array(bv), bounds=[(0, 1), (0, 2), (0, 1), (0, 1)], method='highs').x
lo, hi = 0.0, 0.1
for _ in range(30):
    mid = (lo + hi)/2
    if Bmin(mid)[0] <= 167/192 + 1e-9: hi = mid
    else: lo = mid
print("saturation rho (B_min reaches 167/192): %.5f" % hi, " B_min(1.0) =", Bmin(1.0)[0])
# ---- (b) Liu F(kappa): xi(kappa) smaller root of (30.3), F = (18 xi + 7)/(18 xi + 9)
for k in [sp.Rational(3, 4), sp.Rational(13, 18), sp.Rational(2, 3), sp.Rational(3, 5), sp.Rational(1, 2)]:
    roots = sp.solve((216*k - 18)*d**2 - (468*k - 57)*d + 150*k - 20, d)
    xi = min([float(r) for r in roots])
    print("kappa=%s: xi=%.6f F(kappa)=%.6f  (1+kappa)/2=%.4f" % (k, xi, (18*xi + 7)/(18*xi + 9), float((1 + k)/2)))
# ---- (c) sensitivity of R* at the critical class to the three inputs
# generalized counts: AI(r)=1-d(x+(1-x)r) uses zM=(1-r)/2 -> scale cM*(1-r)/2;  St uses zP=cP*(1-2m)  (cP=2/9 at kappa=3/4);  long: 1-al+(al-d)(t-1)
t, r = sp.symbols('t r')
AI = 1 - d*(r + 2*x*cM*(1 - r)/2)
m = t - r
St = 1 - d*(2*m + 2*x*cP*(1 - 2*m))
Lg = 1 - al + (al - d)*t   # R_long(t) = 1 - alpha + (alpha - delta) t  (OpenAI (20.8), Liu); fixed after referee
rc = sp.solve(sp.Eq(AI, St), r)[0]
Rsh = sp.simplify(AI.subs(r, rc))
tb = sp.solve(sp.Eq(Rsh, Lg), t)
tb = [tt for tt in tb if sp.simplify(tt.subs({cM: 1, cP: sp.Rational(2, 9), al: alpha, x: sp.Rational(1, 2), d: sp.Rational(3, 8)})) > 1][0]
Rgen = sp.simplify(Lg.subs(t, tb))
base = {cM: 1, cP: sp.Rational(2, 9), al: alpha, x: sp.Rational(1, 2)}
dc = (49 - sp.sqrt(921))/48
print("R_gen at base, critical class:", sp.N(Rgen.subs(base).subs(d, dc)), " (check vs R*: ", sp.N(Rstar.subs({x: sp.Rational(1, 2), d: dc})), ")")
for nm, s in [('cM (inverse capacity scale, Lemma 17.1)', cM), ('cP (plain capacity 1/(6kappa)... scale, Lemma 18.1)', cP), ('alpha (amplification slope, Lemma 17.6)', al)]:
    der = sp.diff(Rgen, s).subs(base).subs(d, dc)
    print("  dR*/d[%s] = %.5f" % (nm, float(der)))
print("  reference: cP = 2/9 at kappa=3/4; cP=1/(6kappa)*... actually zP=(1-2m)/(6kappa) so cP=1/(6kappa): kappa=3/4 -> 2/9")
