"""Isolate the zeta-large-value term sup_{tau in [2,tau0]} LV_zeta(sigma,tau)/tau of Cor. 11.7, with and without the
quasi-RH half-plane mu points, on sigma in [0.7, 7/8]. This is the only term the new mu bounds can affect."""
import sys, time
sys.path.insert(0, sys.argv[1])
from fractions import Fraction as frac
from literature import *
from hypotheses import Hypothesis_Set, Hypothesis
from bound_mu import Bound_mu
from functions import Interval
from reference import Reference
from region import Region
from polytope import Polytope
from constants import Constants
import large_values as lv, zeta_large_values as zlv, zero_density_estimate as zd
def H78():
    pts=[(frac(7,8),frac(0))]+[(s, frac(26,63)*(frac(7,8)-s)) for s in [frac(7,10),frac(3,4),frac(4,5),frac(17,20)]]
    return [Hypothesis(f"quasi-RH half-plane bound on \\mu({s})","Upper bound on mu",Bound_mu(s,m),"OpenAI 2026 + convexity",Reference.classical()) for s,m in pts]
SIG = Interval(frac(7,10), frac(7,8))
def zlv_term(with78, tau0):
    h = Hypothesis_Set()
    h.add_hypothesis(lv.large_value_estimate_L2)
    h.add_hypotheses(zlv.get_trivial_zlv())
    h.add_hypotheses(literature.list_hypotheses(hypothesis_type="Zeta large value estimate"))
    h.add_hypotheses(literature.list_hypotheses(hypothesis_type="Upper bound on mu"))
    h.add_hypotheses(literature.list_hypotheses(hypothesis_type="Upper bound on beta"))
    if with78: h.add_hypotheses(H78())
    h.add_hypotheses(zlv.beta_to_zlv(h)); h.add_hypotheses(zlv.mu_to_zlv(h)); h.add_hypotheses(zlv.lv_to_zlv(h))
    h.add_hypotheses(zlv.compute_large_value_estimate(h))
    zlvr = zd.compute_large_value_region(h, Region.from_polytope(Polytope.rect((SIG.x0, SIG.x1), (frac(2), tau0), (0, Constants.LV_DEFAULT_UPPER_BOUND))), zeta=True)
    sup2 = zd.compute_sup_rho_on_tau([r.child for r in zlvr.data.region.child], SIG)
    return sup2
for tau0 in (frac(3), frac(5)):
    for w in (False, True):
        t=time.time(); s2 = zlv_term(w, tau0)
        print(f"tau0={tau0} with_halfplane={w} ({time.time()-t:.0f}s):", flush=True)
        for piece in s2: print("    sup2 =", piece[0], " on ", piece[1], flush=True)
