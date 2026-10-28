# Four notes adjacent to the Riemann hypothesis (October 2026)

**Status: drafts. Each note has been through at least one internal adversarial referee pass by a separate AI instance; none has been
reviewed by a human mathematician. The derivations, computations and reviews were carried out with AI assistance (Claude, Anthropic);
the author takes responsibility for the content. Corrections are welcome.**

1. `li-positivity-threshold.pdf` — *An explicit Li-positivity threshold from the numerical verification of the Riemann hypothesis.*
   Unconditional theorem: λ_n > 0 for all 1 ≤ n ≤ 1 918 555 899 886 294 190 260 224 ≈ 1.92·10^24, from the zero-sum formula, the
   Platt–Trudgian verification height 3·10^12, and the explicit zero count of Hasanalizade–Shen–Wong. Certified in Arb ball arithmetic:
   `lab/certify_li_threshold.py`, output `lab/2026-10-26_certify_li_threshold_v3_output.txt`. Prior rigorous record by direct computation: n ≤ 10^5.

2. `floor-class-barrier.pdf` — *A Lean-checked, counts-independent form of tomoto0's floor-class barrier.*
   **Priority note:** the barrier itself (trivially counted rows near the critical line force the boundary above 13/15, and the detector
   floor alone gives ≥ 0.86979) is due to tomoto0, `reports/barrier_analysis.md` (2026-10-07, in Japanese) in
   github.com/tomoto0/quasi-riemann-hypothesis-7-8-verification; our literature search missed it. What this note adds: the statement inside
   Liu's comparison system (free M, arbitrary witness counts), the exact rational 167/192 as a convex combination of three affine constraints,
   a Lean 4 + Mathlib check of that inequality (`lean/FloorBarrier.lean`), and the absolute-value argument of §3. Sensitivity scripts in `lab/directionG/`.

3. `growth-right-of-78.pdf` — *Growth of ζ and of Dirichlet L-functions to the right of 7/8.*
   Conditional on the Lean-verified half-plane Re s > 7/8: μ(σ) = 0 for σ ≥ 7/8 (previously known only for σ ≥ 1) and
   μ(σ) ≤ (26/63)(7/8 − σ), which improves the sharpest known bounds (ANTEDB Table 6.2) for σ > 1351/1976 ≈ 0.684; conductor-aspect
   interpolations; and a verification, by hand and with the ANTEDB derivation engine, that no zero-density gain below 7/8 follows.
   Scripts in `lab/growth78/`.

4. `quartic-obstruction.pdf` — *The quartic analogue over Z[i] of the cubic-theta argument, and where it stops.*
   The Möbius-absorption identity holds with the quartic symbol over the Gaussian integers (Lemma 1, verified numerically including inert
   primes, `lab/quartic/`), so the first stage would start at 7/8; no automorphic input of the required shape is known, because quartic
   Gauss sums are Whittaker coefficients of the theta on the 4-fold cover of GL_3 and every available transformation has conductor N(h)^3.

**Lean, Li theorem (partial).** `lean/LiPointwise.lean` formalizes the pointwise content of the Li note: the Jordan-type inequality
1 − cos x ≥ 2x²/π², the angle bounds 1/γ − 1/(12γ³) ≤ θ(γ) ≤ 1/γ, the off-line quadruple identity and its bound 4 − 4cosh(n log‖w‖),
the logarithm estimate |log(1+x) − x| ≤ 2x² (|x| ≤ 1/2), and the δ-bound |log‖1 − 1/ρ‖| ≤ (|1−2β| + 2γ⁻²)/(2γ²). All check with
axioms propext/Classical.choice/Quot.sound. `lean/LiAbel.lean` formalizes the Abel-summation step used in Lemmas 3, 4, 4′: for a finite
set of ordinates in (T₀, T] and g of class C¹, Σ g(γ) = card·g(T) − ∫ g′·N(t) dt (`abel_sum`), and the tail inequality
Σ g(γ) ≤ g(T₀)N⁺(T₀) + ∫ g·(N⁺)′ for g ≥ 0 decreasing and any C¹ majorant N⁺ of the counting function (`tail_sum_le`, via
Mathlib's integration by parts). `lean/LiTail.lean` makes this explicit for g = sinh²(a/(4t²)) and N⁺ = M + R − (M(T₀) − R(T₀))
with M, R the main and error terms of the zero-counting formula: `tail_explicit` gives Σ g(γ) ≤ (a²/16)·cosh²(a/(4T₀²))·J(T₀) with
the same J(T₀) as the note and the certificate script (so E*(n) = 4·this with a = nc); all integrals are over [T₀, T], no improper
integral is used. `lean/LiHead.lean` is Lemma 4 (small-angle head bound): for ordinates in (a, T₀] whose counting function is
minorised by M − R − (M(a) + R(a)), `head_sum_ge` gives Σ γ⁻² ≥ S⁻(a) with the same closed form S⁻ as the script (including the
bound log log t ≤ log t for ∫ R t⁻³), and `head_bound` gives Σ 2(1 − cos nθ_γ) ≥ (4n²/π²)(1 − 1/(12a²))² S⁻(a) for n/π ≤ a.
`lean/LiOsc.lean` is Lemma 4′ (oscillatory head bound): `osc_head_bound` gives Σ 2(1 − cos nθ_γ) ≥ A′(n, T₁) for ordinates in
(T₁, T₀] with counting function M + S̃ − (M(T₁) + S̃(T₁)), |S̃| ≤ R, exactly the expression A′ of the note and the script; Bonnet's
mean value theorem is replaced by an integration by parts against sin(nθ) with the increasing weight M′(t)(t² + 1/4)
(`osc_integral_le`). `lean/LiSymm.lean` reduces the finite symmetric zero sum to ordinates γ > 0: for a finite family of zeros
closed under ρ ↦ ρ̄ and ρ ↦ 1 − ρ (given as involutions of the index set, so multiplicities are respected), `partial_sum_ge`
gives Σ Re[1 − (1 − 1/ρ)ⁿ] ≥ Σ_{0<γ≤T₀} 2(1 − cos nθ_γ) − 4 Σ_{γ>T₀} g_{nc}(γ), using 1 − 1/ρ = e^{iθ_γ} on the line
(`online_w`) and Lemma 2 with the δ-bound off the line (`Forb_offline`). NOT formalized: the three analytic inputs (zero-sum
formula and its symmetric exhaustion, verification height, explicit zero count), the final assembly with the counting function
and the interval/chain logic, and the numerical interval chain, which remains an external Arb certificate.
The Lean δ-bound uses the Mathlib-provable constant 2x² (the note proves x²); the certificate passes unchanged with the corresponding
c = 1 + 2·T₀⁻² (same N₀).

Reproduce: `pip install mpmath sympy python-flint scipy`; `python3 lab/certify_li_threshold.py` (< 1 min). Lean: a Mathlib project
(`lake new X math && lake exe cache get`), copy `lean/FloorBarrier.lean`, `lake env lean FloorBarrier.lean`.
