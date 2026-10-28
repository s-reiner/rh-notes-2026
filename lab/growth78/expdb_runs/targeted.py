"""Targeted test: on sigma in [0.684, 7/8], do mu-derived zeta large value estimates from the quasi-RH half-plane
(mu(7/8)=0 and the convexity points) improve the zero-density bound obtainable from the standard inputs?"""
import sys, time
sys.path.insert(0, sys.argv[1])
from fractions import Fraction as frac
from literature import *
from hypotheses import Hypothesis_Set, Hypothesis
from bound_mu import Bound_mu
from functions import Interval, Affine
from reference import Reference
import large_values as lv, zeta_large_values as zlv, zero_density_estimate as zd
t0=time.time()
def stamp(m): print(f"[{time.time()-t0:6.0f}s] {m}", flush=True)
def H78():
    pts=[(frac(7,8),frac(0))]+[(s, frac(26,63)*(frac(7,8)-s)) for s in [frac(7,10),frac(3,4),frac(4,5),frac(17,20)]]
    return [Hypothesis(f"quasi-RH half-plane bound on \\mu({s})","Upper bound on mu",Bound_mu(s,m),"OpenAI 2026 + convexity",Reference.classical()) for s,m in pts]
SIG = Interval(frac(1351,1976), frac(7,8))
def run(with78, label):
    h = Hypothesis_Set()
    h.add_hypothesis(lv.large_value_estimate_L2)
    for k in range(2, 6): h.add_hypothesis(lv.raise_to_power_hypothesis(k))
    # standard large-value inputs relevant in this range
    for kw in ["Guth, Maynard", "Jutila, k = 3", "Bourgain", "Heath-Brown", "Huxley"]:
        try: h.add_hypotheses(literature.list_hypotheses(hypothesis_type="Large value estimate", keywords=kw))
        except Exception as e: pass
    h.add_hypotheses(zlv.get_trivial_zlv())
    h.add_hypotheses(literature.list_hypotheses(hypothesis_type="Zeta large value estimate"))
    h.add_hypotheses(literature.list_hypotheses(hypothesis_type="Upper bound on mu"))
    if with78: h.add_hypotheses(H78())
    mu_zlv = zlv.mu_to_zlv(h)
    h.add_hypotheses(mu_zlv)
    stamp(f"{label}: {len(h.list_hypotheses('Large value estimate'))} LV, {len(h.list_hypotheses('Zeta large value estimate'))} ZLV hypotheses")
    zdt = zd.lv_zlv_to_zd(h, SIG, tau0=frac(3))
    stamp(f"{label}: done")
    for r in zdt: print("    A(x) <=", r.data, flush=True)
    return zdt
run(False, "baseline")
run(True, "with half-plane")
