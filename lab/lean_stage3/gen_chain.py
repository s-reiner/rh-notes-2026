"""
Generate lean/FloorBarrier/FloorBarrier/LiChain.lean: the 89-interval certificate chain of
lab/certify_li_threshold.py, each interval checked in Lean from the enclosures in LiCert.lean.

Every bound emitted here is first re-derived in exact rational arithmetic (Fractions), mirroring the
Lean proof step by step, so that each `linarith`/`norm_num` step is known to close.
Run: python3 gen_chain.py  (needs chain.out from chain.py, and python-flint only for chain.py)
"""
from fractions import Fraction as F
import math, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, '../../lean/FloorBarrier/FloorBarrier/LiChain.lean')
D = 24

def dn(x, d=D): return F(math.floor(x * 10**d), 10**d)
def up(x, d=D): return F(math.ceil(x * 10**d), 10**d)
def dec(x):
    """exact decimal string of a Fraction whose denominator divides a power of 10"""
    neg = x < 0; x = abs(x)
    k = 0
    while (x * 10**k).denominator != 1: k += 1
    i = int(x * 10**k)
    if k == 0: r = str(i)
    else:
        st = str(i).rjust(k + 1, '0'); r = st[:-k] + '.' + st[-k:]
    return ('-' if neg else '') + r
def lit(x):
    """Lean real literal, parenthesised"""
    return '(' + dec(x) + ' : ℝ)'

def logser(r, n):
    x = 1 - r; S = sum(x**(i + 1) / (i + 1) for i in range(n)); e = abs(x)**(n + 1) / (1 - abs(x))
    return (-S - e, -S + e)

C = json.load(open(os.path.join(HERE, 'consts.json')))
L2 = (F(C['L2lo']), F(C['L2hi'])); L3 = (F(C['L3lo']), F(C['L3hi'])); L5 = (F(C['L5lo']), F(C['L5hi']))
LP = (F(C['LPlo']), F(C['LPhi'])); LL0 = (F(C['LL0lo']), F(C['LL0hi']))
Wm = F(C['Wm']); Wp = F(C['Wp'])
Pm = F('3.14159265358979323846'); Pp = F('3.14159265358979323847')
JP = F(53493920955173805339826419034, 10**66)
JP_LEAN = '(53493920955173805339826419034 / 10 ^ 66)'
T0 = F(3 * 10**12); c = 1 + F(2) / T0**2
A1c, A2c = F('0.1038'), F('0.2573')

def lin(co, side):
    """bound for a2*log2 + a3*log3 + a5*log5 + ap*logpi; side 0 = lower, 1 = upper"""
    a2, a3, a5, ap = co; tot = F(0)
    for a, L in ((a2, L2), (a3, L3), (a5, L5), (ap, LP)):
        tot += a * (L[side] if a >= 0 else L[1 - side])
    return tot

def fac235(n):
    e = []
    for p in (2, 3, 5):
        k = 0
        while n % p == 0: n //= p; k += 1
        e.append(k)
    assert n == 1
    return e

lT0 = (lin((12, 1, 12, 0), 0), lin((12, 1, 12, 0), 1))
L0 = (lin((11, 1, 12, -1), 0), lin((11, 1, 12, -1), 1))
R0hi = A1c * lT0[1] + A2c * LL0[1] + F('9.3675')

ATOMS = ("  obtain ⟨a, b⟩ := log2_b; obtain ⟨c, d⟩ := log3_b; obtain ⟨e, f⟩ := log5_b\n"
         "  obtain ⟨g, h⟩ := logpi_b; obtain ⟨w1, w2⟩ := inv2pi_b\n")

def smooth_anchor(x):
    """5-smooth fraction N/D with N/D * x close to 1, N, D >= 2"""
    best = None
    for a in range(-12, 13):
        for b in range(-8, 9):
            for cc in range(-6, 7):
                v = F(2)**a * F(3)**b * F(5)**cc
                err = abs(1 - v * x)
                if v.numerator >= 2 and v.denominator >= 2 and (best is None or err < best[0]):
                    best = (err, v)
    return best[1]

out = []
emit = out.append

# ------------------------------------------------------------------ T1 lemmas
T1s = {}
def t1_lemmas(T1):
    if T1 in T1s: return T1s[T1]
    tag = 't' + str(T1)
    p, q, r = fac235(T1)
    lT1 = (lin((p, q, r, 0), 0), lin((p, q, r, 0), 1))
    anc = smooth_anchor((lT1[0] + lT1[1]) / 2)
    N, Dd = anc.numerator, anc.denominator
    eN, eD = fac235(N), fac235(Dd)
    ancco = tuple(eN[i] - eD[i] for i in range(3))
    rlo = dn(lT1[0] * anc); rhi = up(lT1[1] * anc)
    NT = 10
    x = logser(rlo, NT)[0]; y = logser(rhi, NT)[1]
    shift_lo = lin((-ancco[0], -ancco[1], -ancco[2], 0), 0)
    shift_hi = lin((-ancco[0], -ancco[1], -ancco[2], 0), 1)
    LL1 = (dn(x + shift_lo - F(1, 10**20)), up(y + shift_hi + F(1, 10**20)))
    emit(f'''
/-! ### `T1 = {T1}` -/

theorem logT1_{tag} : log ({T1} : ℝ) = {p} * log 2 + {q} * log 3 + {r} * log 5 := by
  rw [show ({T1} : ℝ) = 2 ^ {p} * 3 ^ {q} * 5 ^ {r} by norm_num, log_235]; push_cast; ring

theorem logL1_{tag} : log (({T1} : ℝ) / (2 * π)) = {p - 1} * log 2 + {q} * log 3 + {r} * log 5 - log π := by
  rw [Real.log_div (by norm_num) (by positivity), Real.log_mul (by norm_num) Real.pi_pos.ne', logT1_{tag}]
  ring

theorem loglogT1_{tag} : {lit(LL1[0])} ≤ log (log ({T1} : ℝ)) ∧ log (log ({T1} : ℝ)) ≤ {lit(LL1[1])} := by
  obtain ⟨a, b⟩ := log2_b; obtain ⟨c, d⟩ := log3_b; obtain ⟨e, f⟩ := log5_b
  have hx := logT1_{tag}
  set x := log ({T1} : ℝ) with hxdef
  have hxpos : 0 < x := by linarith
  have eN : log ({N} : ℝ) = {eN[0]} * log 2 + {eN[1]} * log 3 + {eN[2]} * log 5 := by
    rw [show ({N} : ℝ) = 2 ^ {eN[0]} * 3 ^ {eN[1]} * 5 ^ {eN[2]} by norm_num, log_235]; push_cast; ring
  have eD : log ({Dd} : ℝ) = {eD[0]} * log 2 + {eD[1]} * log 3 + {eD[2]} * log 5 := by
    rw [show ({Dd} : ℝ) = 2 ^ {eD[0]} * 3 ^ {eD[1]} * 5 ^ {eD[2]} by norm_num, log_235]; push_cast; ring
  have id : log (x * {N} / {Dd}) = log x + log ({N} : ℝ) - log ({Dd} : ℝ) := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_mul hxpos.ne' (by norm_num)]
  obtain ⟨h1, -⟩ := log_bounds_of {lit(rlo)} {NT} (by rw [abs_lt]; constructor <;> norm_num)
  obtain ⟨-, h2⟩ := log_bounds_of {lit(rhi)} {NT} (by rw [abs_lt]; constructor <;> norm_num)
  have m1 : log {lit(rlo)} ≤ log (x * {N} / {Dd}) := Real.log_le_log (by norm_num) (by linarith)
  have m2 : log (x * {N} / {Dd}) ≤ log {lit(rhi)} := Real.log_le_log (by positivity) (by linarith)
  rw [id] at m1 m2
  norm_num [Finset.sum_range_succ, abs_of_neg, abs_of_pos] at h1 h2
  constructor <;> linarith
''')
    T1s[T1] = dict(tag=tag, p=p, q=q, r=r, lT1=lT1, LL1=LL1)
    return T1s[T1]

# ------------------------------------------------------------------ A1 interval
def smooth_above(x):
    best = None
    for i in range(80):
        for j in range(50):
            pp = 2**i * 3**j
            if pp > x * 10: break
            k = 0
            while pp * 5**k < x: k += 1
            v = pp * 5**k
            if best is None or v < best: best = v
    return best

def FR(logt, t):  # FR(t) = -(0.3611)(2 log t + 1)/(4 t^2) - 9.3675/(2 t^2)
    return -(A1c + A2c) * (2 * logt + 1) / (4 * t**2) - F('9.3675') / (2 * t**2)

def gen_A1(k, n1, n2):
    a = smooth_above(max(F(n2) / Pm, F(60)))
    assert F(n2) <= a * Pm and a <= T0 and a >= 60
    i, j, m = fac235(a)
    la = (lin((i, j, m, 0), 0), lin((i, j, m, 0), 1))
    La = (lin((i - 1, j, m, -1), 0), lin((i - 1, j, m, -1), 1))
    Glo = dn(-L0[1] / T0 + La[0] / a + (F(1) / a - 1 / T0), 40)
    assert Glo > 0
    Glo = F(Glo.numerator * 999999, Glo.denominator * 1000000)
    Glo = dn(Glo, 40)
    # rest = -R T0/T0^2 - R a/a^2 - 2 (FR T0 - FR a), crude loglog <= log - 1
    R0c = A1c * lT0[1] + A2c * (lT0[1] - 1) + F('9.3675')
    Rac = A1c * la[1] + A2c * (la[1] - 1) + F('9.3675')
    rest = -R0c / T0**2 - Rac / a**2 - 2 * (FR(lT0[0], T0) - FR(la[1], a))
    S = Wm * Glo + rest
    assert S > 0
    Slo = dn(S * F(999, 1000), 40)
    # Lean literal for Slo in scientific form is fine as a decimal
    Klo = 4 * F(n1)**2 / Pp**2 * (1 - 1 / (12 * a**2))**2
    Eup = F(n2)**2 * c**2 / 4 * 4 * JP
    assert Eup < Klo * Slo, (k, n1, n2)
    rest_lo = dn(rest, 40) - F(1, 10**40)
    assert Wm * Glo + rest_lo >= Slo
    emit(f'''
/-! ### Interval {k}: `[{n1}, {n2}]`, head sum, `a = {a} = 2^{i}·3^{j}·5^{m}` -/

theorem S_{k} : {lit(Slo)} ≤ Sminus ({a} : ℝ) T0c := by
{ATOMS}  have h0 := logT0_eq; have hL0 := logL0_eq
  have hA : log ({a} : ℝ) = {i} * log 2 + {j} * log 3 + {m} * log 5 := by
    rw [show ({a} : ℝ) = 2 ^ {i} * 3 ^ {j} * 5 ^ {m} by norm_num, log_235]; push_cast; ring
  have hLa : log (({a} : ℝ) / (2 * π)) = log ({a} : ℝ) - log 2 - log π := by
    rw [Real.log_div (by norm_num) (by positivity), Real.log_mul (by norm_num) Real.pi_pos.ne']; ring
  have hlT0 : 0 < log T0c := by linarith
  have hlA : 0 < log ({a} : ℝ) := by linarith
  have q0 := Real.log_le_sub_one_of_pos hlT0
  have qa := Real.log_le_sub_one_of_pos hlA
  set L0 := log (T0c / (2 * π))
  set La := log (({a} : ℝ) / (2 * π))
  have hEq : Sminus ({a} : ℝ) T0c = (1 / (2 * π)) * (-L0 / T0c + La / {a} + (1 / {a} - 1 / T0c))
      + (-(R T0c) / T0c ^ 2 - R ({a} : ℝ) / ({a} : ℝ) ^ 2 - 2 * (FR T0c - FR ({a} : ℝ))) := by
    simp only [Sminus, M]; ring
  have hG : {lit(Glo)} ≤ -L0 / T0c + La / {a} + (1 / {a} - 1 / T0c) := by linarith
  have hP := mul_le_mul w1 hG (by norm_num) (by positivity)
  have hrest : {lit(rest_lo)} ≤ -(R T0c) / T0c ^ 2 - R ({a} : ℝ) / ({a} : ℝ) ^ 2 - 2 * (FR T0c - FR ({a} : ℝ)) := by
    unfold R FR; linarith
  rw [hEq]; norm_num at hP ⊢; linarith

theorem cert_{k} : Estar ({n2} : ℕ) (1 + 2 / T0c ^ 2) T0c <
    4 * (({n1} : ℕ) : ℝ) ^ 2 / π ^ 2 * (1 - 1 / (12 * ({a} : ℝ) ^ 2)) ^ 2 * Sminus ({a} : ℝ) T0c := by
  have hS := S_{k}
  have hJ := J_b
  have hJ0 : 0 ≤ J T0c := J_nonneg _ (by nlinarith [Real.pi_lt_d20])
  have hp := Real.pi_lt_d20
  have hch : Real.cosh ((({n2} : ℕ) : ℝ) * (1 + 2 / T0c ^ 2) / (4 * T0c ^ 2)) ≤ 2 :=
    cosh_le_two _ (by rw [abs_of_pos (by positivity)]; norm_num)
  unfold Estar
  calc (({n2} : ℕ) : ℝ) ^ 2 * (1 + 2 / T0c ^ 2) ^ 2 / 4
        * Real.cosh ((({n2} : ℕ) : ℝ) * (1 + 2 / T0c ^ 2) / (4 * T0c ^ 2)) ^ 2 * J T0c
      ≤ (({n2} : ℕ) : ℝ) ^ 2 * (1 + 2 / T0c ^ 2) ^ 2 / 4 * 2 ^ 2 * {JP_LEAN} := by
        gcongr
    _ < 4 * (({n1} : ℕ) : ℝ) ^ 2 / (3.14159265358979323847 : ℝ) ^ 2 * (1 - 1 / (12 * ({a} : ℝ) ^ 2)) ^ 2
          * {lit(Slo)} := by
        norm_num
    _ ≤ 4 * (({n1} : ℕ) : ℝ) ^ 2 / π ^ 2 * (1 - 1 / (12 * ({a} : ℝ) ^ 2)) ^ 2 * Sminus ({a} : ℝ) T0c := by
        gcongr
''')
    return dict(kind='A1', n1=n1, n2=n2, a=a)

# ------------------------------------------------------------------ A2 interval
def expsum_up(x, n=12):
    return sum(x**mm / math.factorial(mm) for mm in range(n)) + abs(x)**n * F(n + 1, math.factorial(n) * n)

def gen_A2(k, n1, n2, T1):
    t = t1_lemmas(T1); tag = t['tag']; p, q, r = t['p'], t['q'], t['r']
    L1 = (lin((p - 1, q, r, -1), 0), lin((p - 1, q, r, -1), 1))
    B = 2 * T0 * (L0[0] - 1) - 2 * T1 * (L1[1] - 1) - 4 * L0[1] * (T0**2 + F(1, 4)) / n1
    Bm = dn(B)
    assert Bm > 0
    R1hi = A1c * t['lT1'][1] + A2c * t['LL1'][1] + F('9.3675')
    rhs_m = Wm * Bm - 4 * R0hi - 4 * R1hi - 2 * n2 * R0hi * (1 / F(T1) - 1 / T0)
    RHS = dn(rhs_m) - F(1, 10**12)
    u = n2 * c / (4 * T0**2); U = F(math.ceil(u * 10**30), 10**30)
    assert U <= 1
    chp = up((expsum_up(U) + expsum_up(-U)) / 2)
    Eup = F(n2)**2 * c**2 / 4 * chp**2 * JP
    assert Eup < RHS, (k, n1, n2, float(RHS - Eup))
    R1str = f"0.1038 * ({p} * {dec(L2[1])} + {q} * {dec(L3[1])} + {r} * {dec(L5[1])}) + 0.2573 * {dec(t['LL1'][1])} + 9.3675"
    Ustr = f"({U.numerator} / {U.denominator} : ℝ)"
    emit(f'''
/-! ### Interval {k}: `[{n1}, {n2}]`, oscillatory, `T1 = {T1}` -/

theorem rhs_{k} : {lit(RHS)} ≤ 2 * (M T0c - M ({T1} : ℝ) - 2 * R T0c - 2 * R ({T1} : ℝ))
      - 4 * Mp T0c * (T0c ^ 2 + 1 / 4) / (({n1} : ℕ) : ℝ)
      - 2 * (({n2} : ℕ) : ℝ) * R T0c * (1 / ({T1} : ℝ) - 1 / T0c) := by
{ATOMS}  obtain ⟨k, l⟩ := loglogT0_b; obtain ⟨k', l'⟩ := loglogT1_{tag}
  have h0 := logT0_eq; have h1 := logT1_{tag}; have hL0 := logL0_eq; have hL1 := logL1_{tag}
  set L0 := log (T0c / (2 * π))
  set L1 := log (({T1} : ℝ) / (2 * π))
  have hX : 2 * (M T0c - M ({T1} : ℝ)) - 4 * Mp T0c * (T0c ^ 2 + 1 / 4) / (({n1} : ℕ) : ℝ)
      = (1 / (2 * π)) * (2 * T0c * (L0 - 1) - 2 * {T1} * (L1 - 1)
          - 4 * L0 * (T0c ^ 2 + 1 / 4) / (({n1} : ℕ) : ℝ)) := by
    simp only [M, Mp]; ring
  have hB : {lit(Bm)} ≤ 2 * T0c * (L0 - 1) - 2 * {T1} * (L1 - 1)
      - 4 * L0 * (T0c ^ 2 + 1 / 4) / (({n1} : ℕ) : ℝ) := by
    push_cast; linarith
  have hP := mul_le_mul w1 hB (by norm_num) (by positivity)
  have hR0 : R T0c ≤ 0.1038 * ({dec(L3[1])} + 12 * {dec(L2[1])} + 12 * {dec(L5[1])}) + 0.2573 * {dec(LL0[1])} + 9.3675 := by
    unfold R; linarith
  have hR1 : R ({T1} : ℝ) ≤ {R1str} := by
    unfold R; linarith
  have hcoef : (0 : ℝ) ≤ 2 * (({n2} : ℕ) : ℝ) * (1 / ({T1} : ℝ) - 1 / T0c) := by norm_num
  have hR0n := mul_le_mul_of_nonneg_left hR0 hcoef
  push_cast at hR0n ⊢
  nlinarith [hX, hP, hR0, hR1, hR0n]

theorem cert_{k} : Estar ({n2} : ℕ) (1 + 2 / T0c ^ 2) T0c <
    2 * (M T0c - M ({T1} : ℝ) - 2 * R T0c - 2 * R ({T1} : ℝ)) - 4 * Mp T0c * (T0c ^ 2 + 1 / 4) / (({n1} : ℕ) : ℝ)
      - 2 * (({n2} : ℕ) : ℝ) * R T0c * (1 / ({T1} : ℝ) - 1 / T0c) := by
  have hr := rhs_{k}
  have hJ := J_b
  have hJ0 : 0 ≤ J T0c := J_nonneg _ (by nlinarith [Real.pi_lt_d20])
  have hU : |(({n2} : ℕ) : ℝ) * (1 + 2 / T0c ^ 2) / (4 * T0c ^ 2)| ≤ |{Ustr}| := by
    rw [abs_of_pos (by positivity), abs_of_pos (by norm_num)]; norm_num
  have hc : Real.cosh ((({n2} : ℕ) : ℝ) * (1 + 2 / T0c ^ 2) / (4 * T0c ^ 2)) ≤ {lit(chp)} := by
    refine le_trans (Real.cosh_le_cosh.mpr hU) ?_
    rw [Real.cosh_eq]
    have e1 := abs_le.mp (Real.exp_bound (x := {Ustr}) (by norm_num [abs_of_pos]) (n := 12) (by norm_num))
    have e2 := abs_le.mp (Real.exp_bound (x := -{Ustr}) (by norm_num [abs_of_neg]) (n := 12) (by norm_num))
    norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos, abs_of_neg] at e1 e2
    linarith [e1.2, e2.2]
  unfold Estar
  calc (({n2} : ℕ) : ℝ) ^ 2 * (1 + 2 / T0c ^ 2) ^ 2 / 4
        * Real.cosh ((({n2} : ℕ) : ℝ) * (1 + 2 / T0c ^ 2) / (4 * T0c ^ 2)) ^ 2 * J T0c
      ≤ (({n2} : ℕ) : ℝ) ^ 2 * (1 + 2 / T0c ^ 2) ^ 2 / 4 * {lit(chp)} ^ 2 * {JP_LEAN} := by
        gcongr
    _ < {lit(RHS)} := by norm_num
    _ ≤ _ := hr
''')
    return dict(kind='A2', n1=n1, n2=n2, T1=T1)

# ------------------------------------------------------------------ main
T1MAP = {'T0/2': 1500000000000, 'T0/3': 1000000000000, '2T0/3': 2000000000000,
         'T0/4': 750000000000, 'T0/10': 300000000000}
rows = []
for line in open(os.path.join(HERE, 'chain.out')):
    sp = line.split()
    if len(sp) > 4 and sp[0].isdigit():
        if sp[2] == 'A1': rows.append((int(sp[0]), int(sp[1]), 'A1', None))
        else: rows.append((int(sp[0]), int(sp[1]), 'A2', T1MAP[sp[3]]))
assert len(rows) == 89 and rows[0][0] == 1
for x, y in zip(rows, rows[1:]): assert x[1] == y[0]
N0 = rows[-1][1]

infos = []
for k, (n1, n2, kind, T1) in enumerate(rows, 1):
    infos.append(gen_A1(k, n1, n2) if kind == 'A1' else gen_A2(k, n1, n2, T1))

# ------------------------------------------------------------------ final theorem
HYPS = """{ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (σ1 σ2 : ι → ι)
    (h1s : ∀ i ∈ s, σ1 i ∈ s) (h1inv : ∀ i ∈ s, σ1 (σ1 i) = i)
    (h1ρ : ∀ i ∈ s, ρ (σ1 i) = starRingEnd ℂ (ρ i))
    (h2s : ∀ i ∈ s, σ2 i ∈ s) (h2inv : ∀ i ∈ s, σ2 (σ2 i) = i)
    (h2ρ : ∀ i ∈ s, ρ (σ2 i) = 1 - ρ i)
    (hβ : ∀ i ∈ s, 0 < (ρ i).re ∧ (ρ i).re < 1) (hγ2 : ∀ i ∈ s, 2 ≤ |(ρ i).im|)
    (T : ℝ) (hT : T0c ≤ T) (himT : ∀ i ∈ s, (ρ i).im ≤ T)
    (hline : ∀ i ∈ s, 0 < (ρ i).im → (ρ i).im ≤ T0c → (ρ i).re = 1 / 2)
    (hcount : ∀ t ∈ Set.Icc (60 : ℝ) T, |Ncount s ρ t - M t| ≤ R t)"""
ARGS = "s ρ σ1 σ2 h1s h1inv h1ρ h2s h2inv h2ρ hβ hγ2 T hT himT hline hcount"
COMMON = "s ρ σ1 σ2 h1s h1inv h1ρ h2s h2inv h2ρ hβ hγ2"
fin = ["""
/-! ## Positivity on each interval -/

/-- Gluing two overlapping ranges. -/
theorem glue (P : ℕ → Prop) (a b c : ℕ) (h1 : ∀ n, a ≤ n → n ≤ b → P n)
    (h2 : ∀ n, b ≤ n → n ≤ c → P n) : ∀ n, a ≤ n → n ≤ c → P n := by
  intro n ha hc
  rcases le_total n b with h | h
  · exact h1 n ha h
  · exact h2 n h hc
"""]
for k, inf in enumerate(infos, 1):
    n1, n2 = inf['n1'], inf['n2']
    if inf['kind'] == 'A1':
        a = inf['a']
        call = (f"li_positive_of_A1 {COMMON} T0c T (1 + 2 / T0c ^ 2) ({a} : ℝ) hT0 hT le_rfl himT hline\n"
                f"    (fun t ht => hcount t ⟨le_trans (by norm_num) ht.1, ht.2⟩) {n1} {n2} (by norm_num) (by norm_num)\n"
                f"    (by rw [div_le_iff₀ Real.pi_pos]; push_cast; linarith) cert_{k}")
    else:
        T1 = inf['T1']
        call = (f"li_positive_of_A2 {COMMON} T0c T (1 + 2 / T0c ^ 2) ({T1} : ℝ) hT0 hT le_rfl himT hline\n"
                f"    (fun t ht => hcount t ⟨le_trans (by norm_num) ht.1, ht.2⟩) {n1} {n2} (by norm_num)\n"
                f"    (by linarith) (by norm_num) cert_{k}")
    fin.append(f"""
theorem pos_{k} {HYPS} :
    ∀ n : ℕ, {n1} ≤ n → n ≤ {n2} → 0 < ∑ i ∈ s, (1 - (1 - (ρ i)⁻¹) ^ n).re := by
  have hp := Real.pi_lt_d20
  have hp' := Real.pi_gt_d20
  have hT0 : 2 * π ≤ T0c := by linarith
  exact {call}
""")
P = "(fun n : ℕ => 0 < ∑ i ∈ s, (1 - (1 - (ρ i)⁻¹) ^ n).re)"
fin.append(f"""
/-! ## The chain -/

/-- **Li positivity for `1 ≤ n ≤ N0 = {N0}`**, with every certificate inequality of the
89-interval chain checked in Lean.  Hypotheses: a finite family of zeros closed under `ρ ↦ ρ̄`,
`ρ ↦ 1 - ρ`, in the strip, with `|Im ρ| ≥ 2` and heights `≤ T`; all zeros of height `≤ T0 = 3·10¹²` on the
critical line (input I2); and `|N(t) - M(t)| ≤ R(t)` on `[60, T]` (input I3).  The passage from finite
families to `λₙ` (input I1) is not formalized. -/
theorem li_positive_chain {HYPS} :
    ∀ n : ℕ, 1 ≤ n → n ≤ {N0} → 0 < ∑ i ∈ s, (1 - (1 - (ρ i)⁻¹) ^ n).re := by
""")
for k, inf in enumerate(infos, 1):
    if k == 1:
        fin.append(f"  have g1 := pos_1 {ARGS}\n")
    else:
        fin.append(f"  have g{k} := glue {P} 1 {infos[k-2]['n2']} {inf['n2']} g{k-1} (pos_{k} {ARGS})\n")
fin.append(f"  exact g{len(infos)}\n")

header = f'''/-
The 89-interval certificate chain of `lab/certify_li_threshold.py`, checked in Lean.
GENERATED by `lab/lean_stage3/gen_chain.py` — do not edit by hand.
Each interval `[n₁, n₂]` gets a lemma `cert_k`: the certificate inequality of `li_positive_of_A1`
(head sum, Lemma 4, with a 5-smooth `a ≥ max(n₂/π, 60)`) or `li_positive_of_A2` (oscillatory, Lemma 4′,
with `T1 ∈ {{T0/10, T0/4, T0/3, T0/2, 2T0/3}}`), proved from the enclosures of `LiCert.lean`.
-/
import FloorBarrier.LiCert

open Real Finset

namespace LiThreshold.Cert

local notation "T0c" => (3000000000000 : ℝ)
'''
# T1 lemmas were emitted inline before first use; that's fine (they precede their users).
text = header + ''.join(out) + ''.join(fin) + '\nend LiThreshold.Cert\n'
open(OUT, 'w').write(text)
print('wrote', OUT, len(text.splitlines()), 'lines;', sum(1 for i in infos if i['kind'] == 'A1'), 'A1,',
      sum(1 for i in infos if i['kind'] == 'A2'), 'A2; N0 =', N0)
