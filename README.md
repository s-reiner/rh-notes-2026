# Four notes adjacent to the Riemann hypothesis (October 2026)

**Status: drafts. Each note has been through at least one internal adversarial referee pass by a separate AI instance; none has been
reviewed by a human mathematician. The derivations, computations and reviews were carried out with AI assistance (Claude, Anthropic);
the author takes responsibility for the content. Corrections are welcome.**

1. `li-positivity-threshold.pdf` — *An explicit Li-positivity threshold from the numerical verification of the Riemann hypothesis.*
   Unconditional theorem: λ_n > 0 for all 1 ≤ n ≤ 2 145 319 159 054 990 487 584 768 ≈ 2.15·10^24, from the zero-sum formula, the
   Platt–Trudgian verification height 3·10^12, and the explicit zero count of Bellotti–Wong (Math. Comp. 2025). Certified in Arb ball arithmetic:
   `lab/certify_li_threshold.py`, output `lab/2026-10-28_certify_li_threshold_v4_output.txt`. **Correction (2026-10-28):** versions up to v5 used the
   Hasanalizade–Shen–Wong constant 9.3675, a typo for 9.4925 (Bellotti–Wong, footnote 1); with the corrected constant the old N₀ ≈ 1.92·10^24
   is not reached. v6 uses the sharper Bellotti–Wong bound instead, which gives the N₀ above. Prior rigorous record by direct computation: n ≤ 10^5.

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

**Lean, Li theorem.** `lean/LiPointwise.lean` formalizes the pointwise content of the Li note: the Jordan-type inequality
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
(`online_w`) and Lemma 2 with the δ-bound off the line (`Forb_offline`). `lean/LiMain.lean` assembles everything: with
N(t) = #{i : 0 < Im ρᵢ ≤ t} and the hypothesis |N − M| ≤ R on [a, T] (resp. [T₁, T]), `li_positive_of_A1` and
`li_positive_of_A2` state that if E*(n₂) < A₁(n₁, n₂) (resp. E*(n₂) < A′(n₁, n₂; T₁)), then the partial Li sum
Σᵢ Re[1 − (1 − 1/ρᵢ)ⁿ] over the finite symmetric family is positive for every integer n ∈ [n₁, n₂]. These certificate
inequalities are exactly the ones `lab/certify_li_threshold.py` checks in ball arithmetic for each of the 98 intervals, with
c = 1 + 2·T₀⁻².
The numerical chain is checked in Lean as well. `lean/LiCert.lean` gives rational enclosures of log 2, log 3, log 5 (error
below 10⁻¹⁴, from Mathlib's series bound for log(1 − x)), log π (from Mathlib's 20-digit bounds for π), log log T₀, 1/(2π), and the
tail constant J(T₀). `lean/LiChain.lean` is generated by `lab/lean_stage3/gen_chain.py` and proves the certificate inequality for
each of the 98 intervals (`cert_k`): the head-sum intervals use a = 2^i·3^j·5^m ≥ max(n₂/π, 60), so that log a is an exact
combination of the enclosed logarithms, and the oscillatory intervals use the script's T₁ ∈ {T₀/10, T₀/4, T₀/3, T₀/2, 2T₀/3},
all of the same form; cosh is bounded through Mathlib's Taylor bound for exp. The binding interval
[2145319157057006329659392, 2145319159054990487584768] closes with the same margin as the Arb run (548.5 on a quantity of size
6.18·10¹⁰). The final theorem `li_positive_chain` states: for a finite family of zeros as above, all on the line up to height
T₀ = 3·10¹², with |N − M| ≤ R on [60, T], the partial Li sum is positive for every integer 1 ≤ n ≤ N₀ = 2145319159054990487584768.
Still NOT formalized (stated as hypotheses): (I1) that λₙ is the limit of these partial sums over a symmetric exhaustion of the
zero set; (I2) the verification height T₀ = 3·10¹² (the hypothesis `hline`); (I3) the explicit zero count (the hypothesis
`hcount`). The Lean files check with `lake env lean` against Mathlib for Lean 4.35.0, axioms propext/Classical.choice/Quot.sound
only; they import each other in the order FloorBarrier, LiPointwise, LiAbel, LiTail, LiHead, LiOsc, LiSymm, LiMain, LiCert,
LiChain (place them in a Mathlib project's source directory under the module prefix used in the `import` lines; `LiChain`
takes about one minute).
The Lean δ-bound uses the Mathlib-provable constant 2x² (the note proves x²); the certificate uses the corresponding
c = 1 + 2·T₀⁻² throughout.

Reproduce: `pip install mpmath sympy python-flint scipy`; `python3 lab/certify_li_threshold.py` (< 1 min). Lean: a Mathlib project
(`lake new X math && lake exe cache get`), copy `lean/FloorBarrier.lean`, `lake env lean FloorBarrier.lean`.
