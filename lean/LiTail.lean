/-
The explicit tail bound (Lemma 3 of the Li-positivity note) in Lean: for a finite set of ordinates
in `(T0, T]` whose counting function is majorised by `M + R - (M T0 - R T0)` (M = main term of the
Riemann–von Mangoldt formula, R = the Hasanalizade–Shen–Wong error term), the sum of
`g_a(γ) = sinh²(a/(4γ²))` is at most `(a²/16) cosh²(a/(4T0²)) J(T0)`.  With `a = n c` and the factor 4 of
the note, this is `E*(n)/4`.  All integrals are over the finite interval `[T0, T]`; no improper integral is used.
-/
import FloorBarrier.LiAbel

open MeasureTheory Set Real

namespace LiThreshold

noncomputable section

/-- Main term `M(t) = (t/2π) log(t/(2πe))`. -/
def M (t : ℝ) : ℝ := t / (2 * π) * (Real.log (t / (2 * π)) - 1)
/-- `M'`. -/
def Mp (t : ℝ) : ℝ := Real.log (t / (2 * π)) / (2 * π)
/-- Error term `R(t) = 0.10076 log t + 0.24460 log log t + 8.08344` (Bellotti–Wong 2025, Thm 1.1). -/
def R (t : ℝ) : ℝ := 0.10076 * Real.log t + 0.24460 * Real.log (Real.log t) + 8.08344
/-- `R'`. -/
def Rp (t : ℝ) : ℝ := 0.10076 / t + 0.24460 / (t * Real.log t)
/-- `g_a(t) = sinh²(a/(4t²))`. -/
def gfun (a t : ℝ) : ℝ := Real.sinh (a / (4 * t ^ 2)) ^ 2
/-- `g_a'`. -/
def gfun' (a t : ℝ) : ℝ :=
  2 * Real.sinh (a / (4 * t ^ 2)) * (Real.cosh (a / (4 * t ^ 2)) * (-(a / (2 * t ^ 3))))
/-- The tail constant `J(T0)` of the note. -/
def J (T0 : ℝ) : ℝ := 2 * R T0 / T0 ^ 4 + (Real.log (T0 / (2 * π)) / 3 + 1 / 9) / (2 * π * T0 ^ 3)
  + 0.10076 / (4 * T0 ^ 4) + 0.24460 / (4 * T0 ^ 4 * Real.log T0)
/-- Integrand bound `h(t) = log(t/2π)/(2π t⁴) + K2/t⁵`. -/
def hfun (K2 t : ℝ) : ℝ := Real.log (t / (2 * π)) / (2 * π * t ^ 4) + K2 / t ^ 5
/-- An antiderivative of `hfun`. -/
def Phi (K2 t : ℝ) : ℝ := -((Real.log (t / (2 * π)) / 3 + 1 / 9) / (2 * π * t ^ 3)) - K2 / (4 * t ^ 4)

theorem hasDerivAt_div_two_pi (t : ℝ) : HasDerivAt (fun t : ℝ => t / (2 * π)) (1 / (2 * π)) t := by
  simpa using (hasDerivAt_id t).div_const (2 * π)

theorem hasDerivAt_M (t : ℝ) (ht : 0 < t) : HasDerivAt M (Mp t) t := by
  have hne : t / (2 * π) ≠ 0 := by positivity
  have h1 := hasDerivAt_div_two_pi t
  have h3 := h1.mul ((h1.log hne).sub_const 1)
  convert h3 using 1
  · funext x; simp [M]
  · simp only [Mp]; field_simp <;> ring

theorem hasDerivAt_R (t : ℝ) (ht : 1 < t) : HasDerivAt R (Rp t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h1 := Real.hasDerivAt_log ht0
  have h := ((h1.const_mul 0.10076).add ((h1.log hlog).const_mul 0.24460)).add_const 8.08344
  convert h using 1
  · funext x; simp [R]
  · simp only [Rp]; field_simp <;> ring

theorem continuousAt_Mp (t : ℝ) (ht : 0 < t) : ContinuousAt Mp t := by
  have hne : t / (2 * π) ≠ 0 := by positivity
  exact ((continuousAt_id.div_const (2 * π)).log hne).div_const (2 * π)

theorem continuousAt_Rp (t : ℝ) (ht : 1 < t) : ContinuousAt Rp t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hmul : t * Real.log t ≠ 0 := mul_ne_zero ht0 hlog
  exact (continuousAt_const.div continuousAt_id ht0).add
    (continuousAt_const.div (continuousAt_id.mul (continuousAt_id.log ht0)) hmul)

theorem hasDerivAt_gfun (a t : ℝ) (ht : 0 < t) : HasDerivAt (gfun a) (gfun' a t) t := by
  have h1 : HasDerivAt (fun t : ℝ => a / (4 * t ^ 2)) (-(a / (2 * t ^ 3))) t := by
    have h := (((hasDerivAt_pow 2 t).const_mul 4).inv (by positivity)).const_mul a
    convert h using 1
    · funext x; simp [div_eq_mul_inv]
    · field_simp <;> ring
  have h2 := ((Real.hasDerivAt_sinh _).comp t h1).pow 2
  convert h2 using 1
  · funext x; simp [gfun]
  · simp only [gfun', Function.comp_apply]; push_cast <;> ring

theorem continuousAt_gfun' (a t : ℝ) (ht : 0 < t) : ContinuousAt (gfun' a) t := by
  unfold gfun'
  fun_prop (disch := positivity)

theorem sinh_le_mul_cosh (y : ℝ) (hy : 0 ≤ y) : Real.sinh y ≤ y * Real.cosh y := by
  let f : ℝ → ℝ := fun t => t * Real.cosh t - Real.sinh t
  have hderiv : ∀ t, HasDerivAt f (t * Real.sinh t) t := by
    intro t
    have h := ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t)
    convert h using 1
    · funext t; simp [f]
    · simp only [id]; ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
    · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hderiv t).deriv]
      have h0 : 0 ≤ t := le_of_lt ht
      exact mul_nonneg h0 (Real.sinh_nonneg_iff.mpr h0)
  have h0 : f 0 = 0 := by simp [f]
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
  rw [h0] at this
  simp only [f] at this
  linarith

theorem gfun_nonneg (a t : ℝ) : 0 ≤ gfun a t := by
  simp only [gfun]; positivity

theorem gfun'_nonpos (a t : ℝ) (ha : 0 ≤ a) (ht : 0 < t) : gfun' a t ≤ 0 := by
  simp only [gfun']
  have hu : 0 ≤ a / (4 * t ^ 2) := by positivity
  have hs := Real.sinh_nonneg_iff.mpr hu
  have hc := (Real.cosh_pos (a / (4 * t ^ 2))).le
  have hd : 0 ≤ a / (2 * t ^ 3) := by positivity
  have h1 : 0 ≤ 2 * Real.sinh (a / (4 * t ^ 2)) := by positivity
  have h2 : Real.cosh (a / (4 * t ^ 2)) * (-(a / (2 * t ^ 3))) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hc (neg_nonpos.mpr hd)
  exact mul_nonpos_of_nonneg_of_nonpos h1 h2

/-- `sinh²(a/(4t²)) ≤ (a/(4t²))² cosh²(a/(4T0²))` for `t ≥ T0 > 0`, `a ≥ 0`. -/
theorem gfun_le (a T0 t : ℝ) (ha : 0 ≤ a) (hT0 : 0 < T0) (ht : T0 ≤ t) :
    gfun a t ≤ (a / (4 * t ^ 2)) ^ 2 * Real.cosh (a / (4 * T0 ^ 2)) ^ 2 := by
  have ht0 : 0 < t := lt_of_lt_of_le hT0 ht
  have hu : 0 ≤ a / (4 * t ^ 2) := by positivity
  have hu0 : 0 ≤ a / (4 * T0 ^ 2) := by positivity
  have huu0 : a / (4 * t ^ 2) ≤ a / (4 * T0 ^ 2) := by gcongr
  have h1 := sinh_le_mul_cosh _ hu
  have h2 : Real.cosh (a / (4 * t ^ 2)) ≤ Real.cosh (a / (4 * T0 ^ 2)) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg hu, abs_of_nonneg hu0]; exact huu0
  have hs := Real.sinh_nonneg_iff.mpr hu
  have hc := (Real.cosh_pos (a / (4 * t ^ 2))).le
  simp only [gfun]
  calc Real.sinh (a / (4 * t ^ 2)) ^ 2
      ≤ (a / (4 * t ^ 2) * Real.cosh (a / (4 * t ^ 2))) ^ 2 := by gcongr
    _ ≤ (a / (4 * t ^ 2) * Real.cosh (a / (4 * T0 ^ 2))) ^ 2 := by gcongr
    _ = (a / (4 * t ^ 2)) ^ 2 * Real.cosh (a / (4 * T0 ^ 2)) ^ 2 := by ring

theorem hasDerivAt_Phi (K2 t : ℝ) (ht : 0 < t) : HasDerivAt (Phi K2) (hfun K2 t) t := by
  have hne : t / (2 * π) ≠ 0 := by positivity
  have hlog := (hasDerivAt_div_two_pi t).log hne
  have hA := (hlog.div_const 3).add_const (1 / 9 : ℝ)
  have hB : HasDerivAt (fun t : ℝ => 2 * π * t ^ 3) (2 * π * (3 * t ^ 2)) t := by
    have := (hasDerivAt_pow 3 t).const_mul (2 * π); convert this using 1 <;> push_cast <;> ring
  have hAB := hA.div hB (by positivity)
  have hC : HasDerivAt (fun t : ℝ => 4 * t ^ 4) (4 * (4 * t ^ 3)) t := by
    have := (hasDerivAt_pow 4 t).const_mul 4; convert this using 1 <;> push_cast <;> ring
  have hD := (hC.inv (by positivity)).const_mul K2
  have h := hAB.neg.sub hD
  convert h using 1
  · funext x; simp [Phi, div_eq_mul_inv]
  · simp only [hfun]; field_simp <;> ring

theorem continuousAt_hfun (K2 t : ℝ) (ht : 0 < t) : ContinuousAt (hfun K2) t := by
  unfold hfun
  fun_prop (disch := positivity)

theorem integral_hfun_le (K2 T0 T : ℝ) (hK2 : 0 ≤ K2) (hT0 : 2 * π ≤ T0) (hT : T0 ≤ T) :
    ∫ t in T0..T, hfun K2 t ≤ -Phi K2 T0 := by
  have hpi := Real.pi_pos
  have hpos : 0 < T0 := by linarith
  have hderiv : ∀ t ∈ uIcc T0 T, HasDerivAt (Phi K2) (hfun K2 t) t := by
    intro t ht; rw [uIcc_of_le hT] at ht; exact hasDerivAt_Phi K2 t (by linarith [ht.1])
  have hcont : ContinuousOn (hfun K2) (Icc T0 T) :=
    fun t ht => (continuousAt_hfun K2 t (by linarith [ht.1])).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable_of_Icc hT)]
  have hlog : 0 ≤ Real.log (T / (2 * π)) := by
    apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; linarith
  have hTpos : 0 < T := by linarith
  have h1 : 0 ≤ (Real.log (T / (2 * π)) / 3 + 1 / 9) / (2 * π * T ^ 3) :=
    div_nonneg (by linarith) (by positivity)
  have h2 : 0 ≤ K2 / (4 * T ^ 4) := by positivity
  have : Phi K2 T ≤ 0 := by simp only [Phi]; linarith
  linarith

/-- Pointwise bound for the integrand. -/
theorem integrand_le (a T0 t : ℝ) (ha : 0 ≤ a) (hT0 : 2 * π ≤ T0) (ht : T0 ≤ t) :
    gfun a t * (Mp t + Rp t) ≤
      a ^ 2 / 16 * Real.cosh (a / (4 * T0 ^ 2)) ^ 2 * hfun (0.10076 + 0.24460 / Real.log T0) t := by
  have hpi := Real.pi_gt_three
  have hT0pos : 0 < T0 := by linarith
  have ht0 : 0 < t := by linarith
  have hlogT0 : 0 < Real.log T0 := Real.log_pos (by linarith)
  have hlogt : Real.log T0 ≤ Real.log t := Real.log_le_log hT0pos ht
  have hlt : 0 < Real.log t := lt_of_lt_of_le hlogT0 hlogt
  have hlog2 : 0 ≤ Real.log (t / (2 * π)) := by
    apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; linarith
  have hMR : 0 ≤ Mp t + Rp t := by
    have h1 : 0 ≤ Mp t := div_nonneg hlog2 (by positivity)
    have h2 : 0 ≤ Rp t := add_nonneg (by positivity) (div_nonneg (by norm_num) (mul_nonneg ht0.le hlt.le))
    exact add_nonneg h1 h2
  have hg := gfun_le a T0 t ha hT0pos ht
  have hne1 : t ≠ 0 := ht0.ne'
  have hne2 : Real.log t ≠ 0 := hlt.ne'
  have hne3 : Real.log T0 ≠ 0 := hlogT0.ne'
  have hne4 : π ≠ 0 := Real.pi_pos.ne'
  have key : hfun (0.10076 + 0.24460 / Real.log T0) t - (Mp t + Rp t) / t ^ 4
      = 0.24460 / t ^ 5 * (1 / Real.log T0 - 1 / Real.log t) := by
    simp only [hfun, Mp, Rp]; field_simp; ring
  have hinv : 1 / Real.log t ≤ 1 / Real.log T0 := one_div_le_one_div_of_le hlogT0 hlogt
  have hkey : (Mp t + Rp t) / t ^ 4 ≤ hfun (0.10076 + 0.24460 / Real.log T0) t := by
    have : 0 ≤ 0.24460 / t ^ 5 * (1 / Real.log T0 - 1 / Real.log t) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  have hC : 0 ≤ Real.cosh (a / (4 * T0 ^ 2)) ^ 2 := by positivity
  calc gfun a t * (Mp t + Rp t)
      ≤ (a / (4 * t ^ 2)) ^ 2 * Real.cosh (a / (4 * T0 ^ 2)) ^ 2 * (Mp t + Rp t) :=
        mul_le_mul_of_nonneg_right hg hMR
    _ = a ^ 2 / 16 * Real.cosh (a / (4 * T0 ^ 2)) ^ 2 * ((Mp t + Rp t) / t ^ 4) := by
        field_simp; ring
    _ ≤ a ^ 2 / 16 * Real.cosh (a / (4 * T0 ^ 2)) ^ 2 * hfun (0.10076 + 0.24460 / Real.log T0) t := by
        apply mul_le_mul_of_nonneg_left hkey; positivity

/-- Explicit tail bound: `Σ g_a(γ) ≤ (a²/16) cosh²(a/(4T0²)) J(T0)`. -/
theorem tail_explicit {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a T0 T : ℝ) (ha : 0 ≤ a)
    (hT0 : 2 * π ≤ T0) (hT : T0 ≤ T) (hγ : ∀ i ∈ s, T0 < γ i ∧ γ i ≤ T)
    (hcount : ∀ t ∈ Icc T0 T,
      ((s.filter (fun i => γ i ≤ t)).card : ℝ) ≤ M t + R t - (M T0 - R T0)) :
    ∑ i ∈ s, gfun a (γ i) ≤ a ^ 2 / 16 * Real.cosh (a / (4 * T0 ^ 2)) ^ 2 * J T0 := by
  have hpi := Real.pi_gt_three
  have hT0pos : 0 < T0 := by linarith
  have hT01 : 1 < T0 := by linarith
  have hlogT0 : 0 < Real.log T0 := Real.log_pos hT01
  have he : Real.exp 1 ≤ T0 := by have := Real.exp_one_lt_d9; linarith
  have hlog1 : 1 ≤ Real.log T0 := (Real.le_log_iff_exp_le hT0pos).mpr he
  have hloglog : 0 ≤ Real.log (Real.log T0) := Real.log_nonneg hlog1
  have hR : 0 ≤ R T0 := by simp only [R]; linarith
  set C := Real.cosh (a / (4 * T0 ^ 2)) ^ 2 with hCdef
  have hC : 0 ≤ C := by positivity
  set K2 := 0.10076 + 0.24460 / Real.log T0 with hK2def
  have hK2 : 0 ≤ K2 := by positivity
  -- Abel summation + integration by parts
  have hA := tail_sum_le s γ T0 T hT hγ (gfun a) (gfun' a)
    (fun t ht => hasDerivAt_gfun a t (by linarith [ht.1]))
    (fun t ht => (continuousAt_gfun' a t (by linarith [ht.1])).continuousWithinAt)
    (fun t _ => gfun_nonneg a t)
    (fun t ht => gfun'_nonpos a t ha (by linarith [ht.1]))
    (fun t => M t + R t - (M T0 - R T0)) (fun t => Mp t + Rp t)
    (fun t ht => ((hasDerivAt_M t (by linarith [ht.1])).add (hasDerivAt_R t (by linarith [ht.1]))).sub_const _)
    (fun t ht => ((continuousAt_Mp t (by linarith [ht.1])).add
      (continuousAt_Rp t (by linarith [ht.1]))).continuousWithinAt)
    hcount
  -- boundary term
  have hb : gfun a T0 * (M T0 + R T0 - (M T0 - R T0)) ≤ (a / (4 * T0 ^ 2)) ^ 2 * C * (2 * R T0) := by
    have := gfun_le a T0 T0 ha hT0pos le_rfl
    have e : M T0 + R T0 - (M T0 - R T0) = 2 * R T0 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right this (by linarith)
  -- integral term
  have hint1 : IntervalIntegrable (fun t => gfun a t * (Mp t + Rp t)) volume T0 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    exact (((hasDerivAt_gfun a t (by linarith)).continuousAt).mul
      ((continuousAt_Mp t (by linarith)).add (continuousAt_Rp t ht1))).continuousWithinAt
  have hint2 : IntervalIntegrable (fun t => a ^ 2 / 16 * C * hfun K2 t) volume T0 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    intro t ht
    exact (continuousAt_const.mul (continuousAt_hfun K2 t (by linarith [ht.1]))).continuousWithinAt
  have hmono : ∫ t in T0..T, gfun a t * (Mp t + Rp t) ≤ ∫ t in T0..T, a ^ 2 / 16 * C * hfun K2 t := by
    apply intervalIntegral.integral_mono_on hT hint1 hint2
    intro t ht
    exact integrand_le a T0 t ha hT0 ht.1
  rw [intervalIntegral.integral_const_mul] at hmono
  have hI := integral_hfun_le K2 T0 T hK2 hT0 hT
  have hI' : a ^ 2 / 16 * C * ∫ t in T0..T, hfun K2 t ≤ a ^ 2 / 16 * C * (-Phi K2 T0) :=
    mul_le_mul_of_nonneg_left hI (by positivity)
  -- assemble
  have heq : (a / (4 * T0 ^ 2)) ^ 2 * C * (2 * R T0) + a ^ 2 / 16 * C * (-Phi K2 T0)
      = a ^ 2 / 16 * C * J T0 := by
    have hne3 : Real.log T0 ≠ 0 := hlogT0.ne'
    have hne4 : π ≠ 0 := Real.pi_pos.ne'
    have hne5 : T0 ≠ 0 := hT0pos.ne'
    simp only [J, Phi, hK2def]; field_simp; ring
  linarith

end

end LiThreshold
