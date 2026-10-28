/-
The small-angle head bound (Lemma 4 of the Li-positivity note) in Lean.  For a finite set of ordinates in
`(a, T0]` whose counting function is minorised by `M - R - (M a + R a)`, the sum of `γ⁻²` is at least the
explicit `S⁻(a)` of the note (same closed form as the certificate script, including the bound
`log log t ≤ log t` for `∫ R t⁻³`), and hence, for `n/π ≤ a`, the sum of `2(1 - cos(n θ_γ))` is at least
`(4n²/π²)(1 - 1/(12a²))² S⁻(a)`.
-/
import FloorBarrier.LiTail
import FloorBarrier.LiPointwise

open MeasureTheory Set Real

namespace LiThreshold

noncomputable section

/-- Lower-bound form of Abel summation: `g ≥ 0` at `T`, `g' ≤ 0`, `Nlow ≤ count`. -/
theorem head_sum_ge_raw {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a T : ℝ) (hT : a ≤ T)
    (hγ : ∀ i ∈ s, a < γ i ∧ γ i ≤ T)
    (g g' : ℝ → ℝ) (hg : ∀ t ∈ Icc a T, HasDerivAt g (g' t) t) (hg' : ContinuousOn g' (Icc a T))
    (hgT : 0 ≤ g T) (hgdec : ∀ t ∈ Icc a T, g' t ≤ 0)
    (Nlow : ℝ → ℝ) (hNc : ContinuousOn Nlow (Icc a T))
    (hcount : ∀ t ∈ Icc a T, Nlow t ≤ ((s.filter (fun i => γ i ≤ t)).card : ℝ)) :
    Nlow T * g T - ∫ t in a..T, g' t * Nlow t ≤ ∑ i ∈ s, g (γ i) := by
  rw [abel_sum s γ a T hγ g g' hg hg']
  have hcard_int : IntegrableOn (fun t => g' t * ((s.filter (fun i => γ i ≤ t)).card : ℝ)) (Ioc a T) := by
    have : (fun t => g' t * ((s.filter (fun i => γ i ≤ t)).card : ℝ))
        = fun t => ∑ i ∈ s, (Ici (γ i)).indicator g' t := by
      funext t; rw [Finset.card_filter]; push_cast; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      simp only [indicator_apply, mem_Ici]; split_ifs <;> simp
    rw [this]
    exact integrable_finset_sum s (fun i _ =>
      ((hg'.integrableOn_Icc).mono_set Ioc_subset_Icc_self).indicator measurableSet_Ici)
  have hgN_int : IntegrableOn (fun t => g' t * Nlow t) (Ioc a T) :=
    ((hg'.mul hNc).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hstep1 : ∫ t in Ioc a T, g' t * ((s.filter (fun i => γ i ≤ t)).card : ℝ)
      ≤ ∫ t in Ioc a T, g' t * Nlow t := by
    apply setIntegral_mono_on hcard_int hgN_int measurableSet_Ioc
    intro t ht
    have ht' : t ∈ Icc a T := Ioc_subset_Icc_self ht
    have := hgdec t ht'
    have := hcount t ht'
    nlinarith
  have hcardT : ((s.filter (fun i => γ i ≤ T)).card : ℝ) = s.card := by
    congr 1; apply congrArg; apply Finset.filter_true_of_mem; intro i hi; exact (hγ i hi).2
  have hNT : Nlow T ≤ (s.card : ℝ) := by rw [← hcardT]; exact hcount T ⟨hT, le_rfl⟩
  have e1 : ∫ t in Ioc a T, g' t * Nlow t = ∫ t in a..T, g' t * Nlow t :=
    (intervalIntegral.integral_of_le hT).symm
  rw [e1] at hstep1
  have := mul_le_mul_of_nonneg_right hNT hgT
  linarith

/-- `Fm' = 2M/t³`. -/
def Fm (t : ℝ) : ℝ := -(Real.log (t / (2 * π))) / (π * t)
/-- `FR' = (0.3611 log t + 9.3675)/t³ ≥ R/t³`. -/
def FR (t : ℝ) : ℝ := -(0.1038 + 0.2573) * (2 * Real.log t + 1) / (4 * t ^ 2) - 9.3675 / (2 * t ^ 2)
/-- `S⁻(a)` of the note. -/
def Sminus (a T0 : ℝ) : ℝ := (M T0 - R T0) / T0 ^ 2 - (M a + R a) / a ^ 2
  + (Real.log (a / (2 * π)) / a - Real.log (T0 / (2 * π)) / T0) / π - 2 * (FR T0 - FR a)
/-- Combined antiderivative for the integral in Lemma 4, `K = M a + R a`. -/
def PhiH (K t : ℝ) : ℝ := -Fm t + 2 * FR t - K / t ^ 2
def PhiH' (K t : ℝ) : ℝ :=
  -(2 * M t / t ^ 3) + 2 * (((0.1038 + 0.2573) * Real.log t + 9.3675) / t ^ 3) + 2 * K / t ^ 3

theorem hasDerivAt_Fm (t : ℝ) (ht : 0 < t) : HasDerivAt Fm (2 * M t / t ^ 3) t := by
  have hne : t / (2 * π) ≠ 0 := by positivity
  have hlog := (hasDerivAt_div_two_pi t).log hne
  have hB : HasDerivAt (fun t : ℝ => π * t) π t := by simpa using (hasDerivAt_id t).const_mul π
  have h := hlog.neg.div hB (by positivity)
  convert h using 1
  · funext x; simp [Fm]
  · simp only [M, Pi.neg_apply]; field_simp <;> ring

theorem hasDerivAt_FR (t : ℝ) (ht : 0 < t) :
    HasDerivAt FR (((0.1038 + 0.2573) * Real.log t + 9.3675) / t ^ 3) t := by
  have ht0 : t ≠ 0 := ht.ne'
  have h1 := ((Real.hasDerivAt_log ht0).const_mul (2 : ℝ)).add_const (1 : ℝ)
  have h2 := h1.const_mul (-(0.1038 + 0.2573) : ℝ)
  have hB : HasDerivAt (fun t : ℝ => 4 * t ^ 2) (4 * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul (4 : ℝ); convert this using 1 <;> push_cast <;> ring
  have h3 := h2.div hB (by positivity)
  have hC : HasDerivAt (fun t : ℝ => 2 * t ^ 2) (2 * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul (2 : ℝ); convert this using 1 <;> push_cast <;> ring
  have h4 := (hC.inv (by positivity)).const_mul (9.3675 : ℝ)
  have h := h3.sub h4
  convert h using 1
  · funext x; simp [FR, div_eq_mul_inv]
  · field_simp <;> ring

theorem hasDerivAt_PhiH (K t : ℝ) (ht : 0 < t) : HasDerivAt (PhiH K) (PhiH' K t) t := by
  have h1 := hasDerivAt_Fm t ht
  have h2 := hasDerivAt_FR t ht
  have h3 : HasDerivAt (fun t : ℝ => K / t ^ 2) (-(2 * K / t ^ 3)) t := by
    have := ((hasDerivAt_pow 2 t).inv (by positivity)).const_mul K
    convert this using 1
    · funext x; simp [div_eq_mul_inv]
    · field_simp <;> ring
  have h := (h1.neg.add (h2.const_mul (2 : ℝ))).sub h3
  convert h using 1
  · funext x; simp [PhiH]
  · simp only [PhiH']; ring

theorem R_le (t : ℝ) (ht : 1 < t) : R t ≤ (0.1038 + 0.2573) * Real.log t + 9.3675 := by
  have hlt : 0 < Real.log t := Real.log_pos ht
  have := Real.log_le_sub_one_of_pos hlt
  simp only [R]; linarith

/-- Lemma 4, counting part: `Σ γ⁻² ≥ S⁻(a)`. -/
theorem head_sum_ge {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a T0 : ℝ) (ha : 1 < a) (hT : a ≤ T0)
    (hγ : ∀ i ∈ s, a < γ i ∧ γ i ≤ T0)
    (hcount : ∀ t ∈ Icc a T0,
      M t - R t - (M a + R a) ≤ ((s.filter (fun i => γ i ≤ t)).card : ℝ)) :
    Sminus a T0 ≤ ∑ i ∈ s, 1 / (γ i) ^ 2 := by
  have hapos : 0 < a := by linarith
  have hT0pos : 0 < T0 := by linarith
  have hg : ∀ t ∈ Icc a T0, HasDerivAt (fun t : ℝ => 1 / t ^ 2) (-2 / t ^ 3) t := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have := (hasDerivAt_pow 2 t).inv (by positivity)
    convert this using 1
    · funext x; simp [one_div]
    · field_simp <;> ring
  have hg' : ContinuousOn (fun t : ℝ => -2 / t ^ 3) (Icc a T0) := by
    intro t ht
    have : 0 < t := by linarith [ht.1]
    exact (by fun_prop (disch := positivity) : ContinuousAt (fun t : ℝ => -2 / t ^ 3) t).continuousWithinAt
  have hNc : ContinuousOn (fun t => M t - R t - (M a + R a)) (Icc a T0) := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    exact (((hasDerivAt_M t (by linarith)).continuousAt.sub
      (hasDerivAt_R t ht1).continuousAt).sub continuousAt_const).continuousWithinAt
  have hraw := head_sum_ge_raw s γ a T0 hT hγ (fun t => 1 / t ^ 2) (fun t => -2 / t ^ 3) hg hg'
    (by positivity)
    (fun t ht => by
      have : 0 < t := by linarith [ht.1]
      rw [div_le_iff₀ (by positivity)]; linarith)
    (fun t => M t - R t - (M a + R a)) hNc hcount
  beta_reduce at hraw
  -- bound the integral by the FTC for PhiH
  have hint1 : IntervalIntegrable (fun t => -2 / t ^ 3 * (M t - R t - (M a + R a))) volume a T0 :=
    (hg'.mul hNc).intervalIntegrable_of_Icc hT
  have hcontPhi : ContinuousOn (PhiH' (M a + R a)) (Icc a T0) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hM : ContinuousAt M t := (hasDerivAt_M t ht0).continuousAt
    exact (by unfold PhiH'; fun_prop (disch := positivity) : ContinuousAt (PhiH' (M a + R a)) t).continuousWithinAt
  have hint2 : IntervalIntegrable (PhiH' (M a + R a)) volume a T0 := hcontPhi.intervalIntegrable_of_Icc hT
  have hpt : ∀ t ∈ Icc a T0, -2 / t ^ 3 * (M t - R t - (M a + R a)) ≤ PhiH' (M a + R a) t := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : 0 < t := by linarith
    have hR := R_le t ht1
    have hne : t ≠ 0 := ht0.ne'
    have e : PhiH' (M a + R a) t - -2 / t ^ 3 * (M t - R t - (M a + R a))
        = 2 * ((0.1038 + 0.2573) * Real.log t + 9.3675 - R t) / t ^ 3 := by
      simp only [PhiH']; field_simp <;> ring
    have : 0 ≤ 2 * ((0.1038 + 0.2573) * Real.log t + 9.3675 - R t) / t ^ 3 :=
      div_nonneg (by linarith) (by positivity)
    linarith
  have hmono : ∫ t in a..T0, -2 / t ^ 3 * (M t - R t - (M a + R a)) ≤ ∫ t in a..T0, PhiH' (M a + R a) t :=
    intervalIntegral.integral_mono_on hT hint1 hint2 hpt
  have hftc : ∫ t in a..T0, PhiH' (M a + R a) t = PhiH (M a + R a) T0 - PhiH (M a + R a) a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hint2
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact hasDerivAt_PhiH _ t (by linarith [ht.1])
  have heq : (M T0 - R T0 - (M a + R a)) * (1 / T0 ^ 2) - (PhiH (M a + R a) T0 - PhiH (M a + R a) a)
      = Sminus a T0 := by
    have hne1 : a ≠ 0 := hapos.ne'
    have hne2 : T0 ≠ 0 := hT0pos.ne'
    have hne3 : π ≠ 0 := Real.pi_pos.ne'
    simp only [PhiH, Fm, Sminus]; field_simp; ring
  linarith

/-- Per-term Jordan step: for `1 ≤ a`, `n/π ≤ a < γ`. -/
theorem head_term_ge (n : ℕ) (a γ : ℝ) (ha1 : 1 ≤ a) (hna : (n : ℝ) / π ≤ a) (hγ : a < γ) :
    4 * (n : ℝ) ^ 2 / π ^ 2 * (1 - 1 / (12 * a ^ 2)) ^ 2 * (1 / γ ^ 2)
      ≤ 2 * (1 - Real.cos (n * theta γ)) := by
  have hpi := Real.pi_pos
  have hapos : 0 < a := by linarith
  have hγ0 : 0 < γ := by linarith
  have hγ1 : 1 ≤ γ := by linarith
  have hθle := theta_le γ hγ0
  have hθge := theta_ge γ hγ0
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- the lower factor
  have hfa : 0 ≤ 1 - 1 / (12 * a ^ 2) := by
    have : 1 / (12 * a ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    linarith
  have hfaγ : 1 - 1 / (12 * a ^ 2) ≤ 1 - 1 / (12 * γ ^ 2) := by
    have : 1 / (12 * γ ^ 2) ≤ 1 / (12 * a ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith
    linarith
  have hL : (1 / γ) * (1 - 1 / (12 * a ^ 2)) ≤ theta γ := by
    have e : 1 / γ - 1 / (12 * γ ^ 3) = (1 / γ) * (1 - 1 / (12 * γ ^ 2)) := by
      field_simp <;> ring
    have : (1 / γ) * (1 - 1 / (12 * a ^ 2)) ≤ (1 / γ) * (1 - 1 / (12 * γ ^ 2)) :=
      mul_le_mul_of_nonneg_left hfaγ (by positivity)
    linarith
  have hL0 : 0 ≤ (1 / γ) * (1 - 1 / (12 * a ^ 2)) := by positivity
  have hθ0 : 0 ≤ theta γ := le_trans hL0 hL
  -- x := n θ, with 0 ≤ x ≤ π
  have hx0 : 0 ≤ (n : ℝ) * theta γ := mul_nonneg hn0 hθ0
  have hxπ : (n : ℝ) * theta γ ≤ π := by
    have h1 : (n : ℝ) * theta γ ≤ n * (1 / γ) := mul_le_mul_of_nonneg_left hθle hn0
    have h2 : (n : ℝ) * (1 / γ) ≤ n * (1 / a) :=
      mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hapos hγ.le) hn0
    have h3 : (n : ℝ) * (1 / a) ≤ π := by
      rw [← div_eq_mul_one_div, div_le_iff₀ hapos]
      rw [div_le_iff₀ hpi] at hna; linarith
    linarith
  have hJ := one_sub_cos_ge ((n : ℝ) * theta γ) (by rw [abs_of_nonneg hx0]; exact hxπ)
  -- (n L)² ≤ x²
  have hnL : (n : ℝ) * ((1 / γ) * (1 - 1 / (12 * a ^ 2))) ≤ n * theta γ :=
    mul_le_mul_of_nonneg_left hL hn0
  have hnL0 : 0 ≤ (n : ℝ) * ((1 / γ) * (1 - 1 / (12 * a ^ 2))) := mul_nonneg hn0 hL0
  have hsq : ((n : ℝ) * ((1 / γ) * (1 - 1 / (12 * a ^ 2)))) ^ 2 ≤ ((n : ℝ) * theta γ) ^ 2 := by
    gcongr
  have e2 : 4 * (n : ℝ) ^ 2 / π ^ 2 * (1 - 1 / (12 * a ^ 2)) ^ 2 * (1 / γ ^ 2)
      = 2 * (2 * ((n : ℝ) * ((1 / γ) * (1 - 1 / (12 * a ^ 2)))) ^ 2 / π ^ 2) := by
    field_simp; ring
  rw [e2]
  have : 2 * ((n : ℝ) * ((1 / γ) * (1 - 1 / (12 * a ^ 2)))) ^ 2 / π ^ 2
      ≤ 2 * ((n : ℝ) * theta γ) ^ 2 / π ^ 2 := by gcongr
  linarith

/-- Lemma 4: the small-angle head bound. -/
theorem head_bound {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (n : ℕ) (a T0 : ℝ) (ha : 1 < a)
    (hT : a ≤ T0) (hna : (n : ℝ) / π ≤ a) (hγ : ∀ i ∈ s, a < γ i ∧ γ i ≤ T0)
    (hcount : ∀ t ∈ Icc a T0,
      M t - R t - (M a + R a) ≤ ((s.filter (fun i => γ i ≤ t)).card : ℝ)) :
    4 * (n : ℝ) ^ 2 / π ^ 2 * (1 - 1 / (12 * a ^ 2)) ^ 2 * Sminus a T0
      ≤ ∑ i ∈ s, 2 * (1 - Real.cos (n * theta (γ i))) := by
  have hS := head_sum_ge s γ a T0 ha hT hγ hcount
  have hC : 0 ≤ 4 * (n : ℝ) ^ 2 / π ^ 2 * (1 - 1 / (12 * a ^ 2)) ^ 2 := by positivity
  calc 4 * (n : ℝ) ^ 2 / π ^ 2 * (1 - 1 / (12 * a ^ 2)) ^ 2 * Sminus a T0
      ≤ 4 * (n : ℝ) ^ 2 / π ^ 2 * (1 - 1 / (12 * a ^ 2)) ^ 2 * ∑ i ∈ s, 1 / (γ i) ^ 2 :=
        mul_le_mul_of_nonneg_left hS hC
    _ = ∑ i ∈ s, 4 * (n : ℝ) ^ 2 / π ^ 2 * (1 - 1 / (12 * a ^ 2)) ^ 2 * (1 / (γ i) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, 2 * (1 - Real.cos (n * theta (γ i))) := by
        apply Finset.sum_le_sum; intro i hi
        exact head_term_ge n a (γ i) ha.le hna (hγ i hi).1

end

end LiThreshold
