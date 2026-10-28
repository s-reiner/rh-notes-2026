import sympy as sp, numpy as np
from scipy.optimize import linprog, minimize
from fractions import Fraction as Fr

# ---------- Q3: reconstruct -E* from (20.4) and verify Lemma 20.2 ----------
d, y, x, R, q, dd, h, l, M, B = sp.symbols('delta y x R q d h ell M B', real=True)
alpha = sp.Rational(5, 6); z0 = sp.Rational(17, 50)
C0 = sp.Rational(-1, 48); h0 = sp.Rational(13, 16); l0 = sp.Rational(1, 6)
Dx = 3 - sp.Rational(17, 9)*x
Px = (2 - sp.Rational(8, 9)*x)*(1 - x)
J = (alpha - d)*Dx + d*Px
Rstar = 1 - d + (alpha - d)*d*Px/(2*J)
# (20.4) second line at d = h, q = x*delta
E204 = C0 + sp.Rational(2, 3)*d + q/6 - h0*(1 - R)
Estar = E204.subs({q: x*d, R: Rstar})
negE_claim = (1 + (3 + 8*y)*d)/48 - sp.Rational(13, 32)*(alpha - d)*d*Px/J
print("check -E* formula (should be 0):", sp.simplify((-Estar - negE_claim).subs(x, sp.Rational(1, 2) - y)))
py = 7 + 18*y + 8*y**2; jy = 185 + 170*y + (-138 + 12*y + 96*y**2)*d; v = 51 + 41*y
print("Px=py/9:", sp.simplify(Px.subs(x, sp.Rational(1, 2) - y) - py/9), " J=jy/108:", sp.simplify(J.subs(x, sp.Rational(1, 2) - y) - jy/108))
lhs = 10368*v*J.subs(x, sp.Rational(1, 2) - y)*(-Estar.subs(x, sp.Rational(1, 2) - y))
rhs = (3 + 5*y)*((4*v*d - 79)**2 + 49) + 4*y*(4*v*d*((1 + 3*y)*(15 + 32*y)*d + 9 - 13*y) + 265 + 3485*y)
print("identity (20.9) (should be 0):", sp.expand(sp.simplify(lhs - rhs)))

f = sp.lambdify((d, x), -Estar, 'numpy')
ds = np.linspace(0, 5/6, 2001); xs = np.linspace(0, 0.5, 1001)
Dg, Xg = np.meshgrid(ds, xs, indexing='ij'); V = f(Dg, Xg)
i = np.unravel_index(np.argmin(V), V.shape)
print("grid min -E* = %.9e at delta=%.5f x=%.5f" % (V[i], Dg[i], Xg[i]))
res = minimize(lambda p: f(p[0], p[1]), [Dg[i], Xg[i]], bounds=[(1/50, 5/6), (0, 0.5)], method='L-BFGS-B', options={'ftol': 1e-15, 'gtol': 1e-12})
print("refined min -E* = %.9e at delta=%.9f x=%.6f ; 49/440640 = %.9e ; -E(floor,(20.5)) = %.6e ; -E(delta=5/6,(20.7)) = %.6e"
      % (res.fun, res.x[0], res.x[1], 49/440640, 7/1200, 1/48 + (5/6)/16))
dc = (49 - np.sqrt(921))/48
print("Liu delta_c = %.9f ; R*(delta_c,1/2) = %.9f ; -E*(delta_c,1/2) at 7/8 geometry = %.6e" % (dc, float(Rstar.subs({d: dc, x: sp.Rational(1, 2)})), f(dc, 0.5)))
# detector lengths at the critical class
tst = 1 + d*Px/(2*J); rst = ((2 - sp.Rational(8, 9)*x)*tst - sp.Rational(5, 9)*x)/Dx
for nm, ex in [('t*', tst), ('r*', rst), ('m=t-r', tst - rst), ('zM=(1-r)/2', (1 - rst)/2), ('zP=2(1-2m)/9', 2*(1 - 2*(tst - rst))/9),
               ('AI', 1 - d*(x + (1 - x)*rst)), ('St', 1 - d*(sp.Rational(4, 9)*x + (2 - sp.Rational(8, 9)*x)*(tst - rst))), ('L', 1 - d + (alpha - d)*(tst - 1))]:
    print("  %-14s = %.6f" % (nm, float(ex.subs({d: dc, x: sp.Rational(1, 2)}))))

# ---------- general-geometry form of E(h) from (10.15)/(18.4) ----------
a = (1 + d)/2
lx = 1 + l - h; ly = M - lx
EB = a - B + h*(z0 - sp.Rational(1, 6)) - a*ly - l/2 + x*d*l + h*(R + d/2 - z0)
Hclass = 1 + d - (1 + d)*M/2 + d*l*(sp.Rational(1, 2) + x)
print("E_B(h) - [H(delta,x) - B + h(R-2/3)] =", sp.simplify(EB - (Hclass - B + h*(R - sp.Rational(2, 3)))))
# OpenAI special case: M = 5/6, l=1/6, h=13/16, B=7/8  -> C0 + 2delta/3 + q/6 - h(1-R)
print("OpenAI specialisation check:", sp.simplify(EB.subs({M: alpha, l: l0, h: h0, B: sp.Rational(7, 8)}) - (C0 + sp.Rational(2, 3)*d + x*d/6 - h0*(1 - R))))
# sigma0 = 11/12 - l/4 under M + l = 1 from direct bound (15.6)/(22.4), G = b/12, k=0
bb = sp.symbols('b')
lx_g = (1 - bb - l)/2; h_g = 1 - lx_g + l
print("sigma0 = 1 - h/6 + b/12 with b=2h-3l-1 :", sp.simplify((1 - h_g/6 + bb/12)))

# ---------- LP: minimal B given uniform count improvement rho ----------
Rnum = sp.lambdify((d, x), Rstar, 'numpy')
dgrid = np.concatenate([np.linspace(1/50 + 1e-9, 5/6, 240)])
xgrid = np.linspace(0, 0.5, 26)
DG, XG = np.meshgrid(dgrid, xgrid, indexing='ij'); RG = Rnum(DG, XG)
dfl = 1/50  # floor class: R = 1 (no witness), x <= 1/2

def Bmin(rho, hmax=1.0, improve_floor=False):
    # variables: (B, M, l, h); minimise B
    A = []; bvec = []
    A.append([-1, 1/12, -1/6, 0]); bvec.append(-5/6)        # L0 <= B
    A.append([-1, 7/12, 1/3, 0]); bvec.append(-1/3)         # LK <= B
    for Dv, Xv, Rv in zip(DG.ravel(), XG.ravel(), RG.ravel()):
        # 1 + D - (1+D)M/2 + D l (1/2+x) + h (R - rho - 2/3) <= B
        A.append([-1, -(1 + Dv)/2, Dv*(0.5 + Xv), (Rv - rho - 2/3)]); bvec.append(-(1 + Dv))
    Rf = 1 - (rho if improve_floor else 0)
    A.append([-1, -(1 + dfl)/2, dfl*1.0, (Rf - 2/3)]); bvec.append(-(1 + dfl))  # floor, x=1/2
    # geometric: h >= 1 - M/2 + l (b>0); h >= 1 + 2l - M (ly > l); h <= hmax (lx > l)
    A.append([0, -1/2, 1, -1]); bvec.append(-1)
    A.append([0, -1, 2, -1]); bvec.append(-1)
    A.append([0, 0, 0, 1]); bvec.append(hmax)
    r = linprog(c=[1, 0, 0, 0], A_ub=np.array(A), b_ub=np.array(bvec),
                bounds=[(0, 1), (0, 2), (0, 1), (0, 1)], method='highs')
    Bv, Mv, lv, hv = r.x
    cls = np.array(A[2:-4]) @ r.x - np.array(bvec[2:-4])
    k = np.argmax(cls);
    return Bv, Mv, lv, hv, (DG.ravel()[k], XG.ravel()[k], RG.ravel()[k]), cls.max()

print("\nrho=0:", Bmin(0.0)[:4], " binding class:", Bmin(0.0)[4], " Balg=0.874957069799")
for target in [5/6, 0.86, 0.85]:
    lo, hi = 0.0, 0.6
    for _ in range(30):
        mid = (lo + hi)/2
        if Bmin(mid)[0] <= target: hi = mid
        else: lo = mid
    Bv, Mv, lv, hv, cl, _ = Bmin(hi)
    bv = 2*hv - 2 - 2*lv + Mv  # b = ly - lx, lx = 1+l-h, ly = M - lx
    print("target B=%.6f: rho_min=%.6f -> B=%.6f M=%.5f l=%.5f h=%.5f b=%.5f lx=%.5f ly=%.5f ; binding class (delta,x,R*)=(%.4f,%.3f,%.4f) R'=%.4f"
          % (target, hi, Bv, Mv, lv, hv, bv, 1 + lv - hv, Mv - 1 - lv + hv, cl[0], cl[1], cl[2], cl[2] - hi))
print("\n(variant) floor also improved by rho:")
for target in [5/6, 0.86, 0.85]:
    lo, hi = 0.0, 0.6
    for _ in range(30):
        mid = (lo + hi)/2
        if Bmin(mid, improve_floor=True)[0] <= target: hi = mid
        else: lo = mid
    print("  target B=%.6f: rho_min=%.6f" % (target, hi), Bmin(hi, improve_floor=True)[1:5])
# Closed form candidate: with H constraint relaxed at critical class only, what does LP give?
print("\nB_min as function of rho:")
for rho in [0, 0.01, 0.02, 0.04, 0.06, 0.08, 0.1, 0.15, 0.2]:
    Bv, Mv, lv, hv, cl, _ = Bmin(rho)
    print("  rho=%.3f B=%.6f M=%.4f l=%.4f h=%.4f class=(%.4f,%.2f,R*=%.4f)" % (rho, Bv, Mv, lv, hv, cl[0], cl[1], cl[2]))
