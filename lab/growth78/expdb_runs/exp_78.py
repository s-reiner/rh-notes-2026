"""Experiment: feed mu(sigma)=0 for sigma >= 7/8 (quasi-RH half-plane, OpenAI 2026, Lemma 4.9) into the ANTEDB
derivation engine and see (A) the best piecewise mu bound, (B) the best derived zero-density estimate, with and without it."""
import sys, time
sys.path.insert(0, sys.argv[1])          # path to expdb/blueprint/src/python
from fractions import Fraction as frac
from literature import *
import derived
from hypotheses import Hypothesis_Set, Hypothesis
from bound_mu import *
from functions import Interval
from reference import Reference
import large_values as lv, zeta_large_values as zlv, zero_density_estimate as zd

def H78_points():
    pts=[(frac(7,8),frac(0))]
    for s in [frac(7,10),frac(3,4),frac(4,5),frac(17,20)]:
        pts.append((s, frac(26,63)*(frac(7,8)-s)))
    return [Hypothesis(f"quasi-RH half-plane bound on \\mu({s})", "Upper bound on mu", Bound_mu(s,m),
                       "OpenAI 2026 Thm 1.1 + Lemma 4.9 (global assertion); convexity", Reference.classical()) for s,m in pts]

print("=== (A) best piecewise mu bound on [1/2, 9/10]")
hyp = Hypothesis_Set()
hyp.add_hypotheses(literature.list_hypotheses(hypothesis_type="Upper bound on mu"))
hyp.add_hypotheses(derived.derive_all_literature_mu_bounds())
base = best_mu_bound_piecewise(Interval(frac(1,2), frac(9,10)), hyp)
print("baseline:"); [print("   mu(x) <=", b) for b in base]
hyp.add_hypotheses(H78_points())
new = best_mu_bound_piecewise(Interval(frac(1,2), frac(9,10)), hyp)
print("with half-plane:"); [print("   mu(x) <=", b) for b in new]

def zd_run(with78):
    h = Hypothesis_Set()
    h.add_hypothesis(lv.large_value_estimate_L2)
    h.add_hypotheses(literature.list_hypotheses(hypothesis_type="Large value estimate"))
    for k in range(2, 15): h.add_hypothesis(lv.raise_to_power_hypothesis(k))
    h.add_hypotheses(zlv.get_trivial_zlv())
    h.add_hypotheses(literature.list_hypotheses(hypothesis_type="Zeta large value estimate"))
    h.add_hypotheses(literature.list_hypotheses(hypothesis_type="Zero density estimate"))
    h.add_hypotheses(literature.list_hypotheses(hypothesis_type="Upper bound on beta"))
    h.add_hypotheses(literature.list_hypotheses(hypothesis_type="Upper bound on mu"))
    if with78: h.add_hypotheses(H78_points())
    h.add_hypotheses(zlv.beta_to_zlv(h)); h.add_hypotheses(zlv.mu_to_zlv(h)); h.add_hypotheses(zlv.lv_to_zlv(h))
    t0=time.time()
    zdt = zd.lv_zlv_to_zd(h, Interval(frac(1,2), 1), tau0=frac(5))
    print(f"   ({time.time()-t0:.0f}s)")
    return zdt

print("=== (B) best derived zero-density estimate A(x)(1-x) <= ..., baseline")
for r in zd_run(False): print("   ", r.data)
print("=== (B') with half-plane mu bounds")
for r in zd_run(True): print("   ", r.data)
