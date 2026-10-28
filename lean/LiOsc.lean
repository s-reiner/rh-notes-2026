/-
The oscillatory head bound (Lemma 4' of the Li-positivity note) in Lean.  Bonnet's second mean value
theorem is replaced by an integration by parts against `sin(nθ(t))` with the nonnegative increasing weight
`ψ(t) = M'(t)(t² + 1/4)`, which gives the same bound `|∫ cos(nθ) M'| ≤ 2ψ(T0)/n`.
-/
import FloorBarrier.LiHead

open MeasureTheory Set Real

namespace LiThreshold

noncomputable section

/-- `θ'(t) = -1/(t² + 1/4)`. -/
theorem hasDerivAt_theta (t : ℝ) (ht : 0 < t) : HasDerivAt theta (-(1 / (t ^ 2 + 1 / 4))) t := by
  have hne : (2 * t) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => 1 / (2 * t)) (-(1 / (2 * t ^ 2))) t := by
    have := ((hasDerivAt_id' t).const_mul (2 : ℝ)).inv hne
    convert this using 1
    · funext x; simp [one_div]
    · field_simp <;> ring
  have h2 := ((Real.hasDerivAt_arctan _).comp t h1).const_mul (2 : ℝ)
  convert h2 using 1
  · funext x; simp [theta]
  · field_simp <;> ring

/-- `cos(nθ)' = n sin(nθ)/(t² + 1/4)`. -/
theorem hasDerivAt_cos_ntheta (n : ℕ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun t => Real.cos (n * theta t)) (n * Real.sin (n * theta t) / (t ^ 2 + 1 / 4)) t := by
  have h1 := (hasDerivAt_theta t ht).const_mul (n : ℝ)
  have h2 := (Real.hasDerivAt_cos _).comp t h1
  convert h2 using 1
  · funext x; simp [Function.comp]
  · field_simp <;> ring

/-- `sin(nθ)' = -n cos(nθ)/(t² + 1/4)`. -/
theorem hasDerivAt_sin_ntheta (n : ℕ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun t => Real.sin (n * theta t)) (-(n * Real.cos (n * theta t) / (t ^ 2 + 1 / 4))) t := by
  have h1 := (hasDerivAt_theta t ht).const_mul (n : ℝ)
  have h2 := (Real.hasDerivAt_sin _).comp t h1
  convert h2 using 1
  · funext x; simp [Function.comp]
  · field_simp <;> ring

/-- `ψ(t) = M'(t)(t² + 1/4)`. -/
def psi (t : ℝ) : ℝ := Mp t * (t ^ 2 + 1 / 4)
def psi' (t : ℝ) : ℝ := 1 / (2 * π * t) * (t ^ 2 + 1 / 4) + Mp t * (2 * t)

theorem hasDerivAt_Mp (t : ℝ) (ht : 0 < t) : HasDerivAt Mp (1 / (2 * π * t)) t := by
  have hne : t / (2 * π) ≠ 0 := by positivity
  have h := ((hasDerivAt_div_two_pi t).log hne).div_const (2 * π)
  convert h using 1
  · funext x; simp [Mp]
  · field_simp <;> ring

theorem hasDerivAt_psi (t : ℝ) (ht : 0 < t) : HasDerivAt psi (psi' t) t := by
  have h1 := hasDerivAt_Mp t ht
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 + 1 / 4) (2 * t) t := by
    have := (hasDerivAt_pow 2 t).add_const (1 / 4 : ℝ); convert this using 1 <;> push_cast <;> ring
  have h := h1.mul h2
  convert h using 1
  · funext x; simp [psi]
  · simp only [psi']

theorem Mp_nonneg (t : ℝ) (ht : 2 * π ≤ t) : 0 ≤ Mp t := by
  have hpi := Real.pi_pos
  apply div_nonneg _ (by positivity)
  apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; linarith

theorem psi'_nonneg (t : ℝ) (ht : 2 * π ≤ t) : 0 ≤ psi' t := by
  have hpi := Real.pi_pos
  have ht0 : 0 < t := by linarith
  have := Mp_nonneg t ht
  simp only [psi']; positivity

theorem continuousAt_theta (t : ℝ) (ht : 0 < t) : ContinuousAt theta t :=
  (hasDerivAt_theta t ht).continuousAt

/-- `|∫_{T1}^{T0} cos(nθ) M'| ≤ 2ψ(T0)/n` (the Bonnet step, by parts). -/
theorem osc_integral_le (n : ℕ) (hn : 1 ≤ n) (T1 T0 : ℝ) (hT1 : 2 * π ≤ T1) (hT : T1 ≤ T0) :
    |∫ t in T1..T0, Real.cos (n * theta t) * Mp t| ≤ 2 * psi T0 / n := by
  have hpi := Real.pi_pos
  have hT1pos : 0 < T1 := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcontpsi' : ContinuousOn psi' (Icc T1 T0) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hM : ContinuousAt Mp t := (hasDerivAt_Mp t ht0).continuousAt
    exact (by unfold psi'; fun_prop (disch := positivity) : ContinuousAt psi' t).continuousWithinAt
  have hcontpsi : ContinuousOn psi (Icc T1 T0) :=
    fun t ht => (hasDerivAt_psi t (by linarith [ht.1])).continuousAt.continuousWithinAt
  have hcontsin : ContinuousOn (fun t => Real.sin (n * theta t)) (Icc T1 T0) :=
    fun t ht => (hasDerivAt_sin_ntheta n t (by linarith [ht.1])).continuousAt.continuousWithinAt
  have hcontsin' : ContinuousOn (fun t => -(n * Real.cos (n * theta t) / (t ^ 2 + 1 / 4))) (Icc T1 T0) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hθ := continuousAt_theta t ht0
    exact (by fun_prop (disch := positivity) :
      ContinuousAt (fun t => -((n : ℝ) * Real.cos (n * theta t) / (t ^ 2 + 1 / 4))) t).continuousWithinAt
  have hint1 : IntervalIntegrable (fun t => psi' t * Real.sin (n * theta t)) volume T1 T0 :=
    (hcontpsi'.mul hcontsin).intervalIntegrable_of_Icc hT
  have hint2 : IntervalIntegrable (fun t => psi t * (-(n * Real.cos (n * theta t) / (t ^ 2 + 1 / 4))))
      volume T1 T0 :=
    (hcontpsi.mul hcontsin').intervalIntegrable_of_Icc hT
  have hibp : ∫ t in T1..T0, (psi' t * Real.sin (n * theta t)
      + psi t * (-(n * Real.cos (n * theta t) / (t ^ 2 + 1 / 4))))
      = psi T0 * Real.sin (n * theta T0) - psi T1 * Real.sin (n * theta T1) := by
    apply intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    · rw [uIcc_of_le hT]; exact hcontpsi
    · rw [uIcc_of_le hT]; exact hcontsin
    · intro t ht
      rw [min_eq_left hT, max_eq_right hT] at ht
      exact hasDerivAt_psi t (by linarith [ht.1])
    · intro t ht
      rw [min_eq_left hT, max_eq_right hT] at ht
      exact hasDerivAt_sin_ntheta n t (by linarith [ht.1])
    · exact hcontpsi'.intervalIntegrable_of_Icc hT
    · exact hcontsin'.intervalIntegrable_of_Icc hT
  rw [intervalIntegral.integral_add hint1 hint2] at hibp
  have hcongr : ∫ t in T1..T0, Real.cos (n * theta t) * Mp t
      = ∫ t in T1..T0, (-(1 / (n : ℝ))) * (psi t * (-(n * Real.cos (n * theta t) / (t ^ 2 + 1 / 4)))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hT] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hne : (n : ℝ) ≠ 0 := hn0.ne'
    simp only [psi]; field_simp <;> ring
  rw [hcongr, intervalIntegral.integral_const_mul]
  have hFTC : ∫ t in T1..T0, psi' t = psi T0 - psi T1 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hcontpsi'.intervalIntegrable_of_Icc hT)
    intro t ht; rw [uIcc_of_le hT] at ht; exact hasDerivAt_psi t (by linarith [ht.1])
  have hbound : |∫ t in T1..T0, psi' t * Real.sin (n * theta t)| ≤ psi T0 - psi T1 := by
    rw [← hFTC, ← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hT _ (hcontpsi'.intervalIntegrable_of_Icc hT)
    apply Filter.Eventually.of_forall
    intro t ht
    have hp := psi'_nonneg t (by linarith [ht.1])
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
    calc psi' t * |Real.sin (n * theta t)| ≤ psi' t * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hp
      _ = psi' t := mul_one _
  have hpsiT0 : 0 ≤ psi T0 := by
    simp only [psi]; have := Mp_nonneg T0 (by linarith); positivity
  have hpsiT1 : 0 ≤ psi T1 := by
    simp only [psi]; have := Mp_nonneg T1 hT1; positivity
  have e0 := abs_le.mp (Real.abs_sin_le_one (n * theta T0))
  have e1 := abs_le.mp (Real.abs_sin_le_one (n * theta T1))
  have hb := abs_le.mp hbound
  have hI : ∫ t in T1..T0, psi t * (-(n * Real.cos (n * theta t) / (t ^ 2 + 1 / 4)))
      = psi T0 * Real.sin (n * theta T0) - psi T1 * Real.sin (n * theta T1)
        - ∫ t in T1..T0, psi' t * Real.sin (n * theta t) := by linarith
  rw [hI, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / n)]
  have hA : |psi T0 * Real.sin (n * theta T0) - psi T1 * Real.sin (n * theta T1)
      - ∫ t in T1..T0, psi' t * Real.sin (n * theta t)| ≤ 2 * psi T0 := by
    rw [abs_le]
    have p1 := mul_le_mul_of_nonneg_left e0.2 hpsiT0
    have p2 := mul_le_mul_of_nonneg_left e0.1 hpsiT0
    have p3 := mul_le_mul_of_nonneg_left e1.2 hpsiT1
    have p4 := mul_le_mul_of_nonneg_left e1.1 hpsiT1
    constructor <;> linarith
  calc 1 / (n : ℝ) * |psi T0 * Real.sin (n * theta T0) - psi T1 * Real.sin (n * theta T1)
          - ∫ t in T1..T0, psi' t * Real.sin (n * theta t)|
      ≤ 1 / n * (2 * psi T0) := mul_le_mul_of_nonneg_left hA (by positivity)
    _ = 2 * psi T0 / n := by ring

/-- Integrability of `g' · count` on `[T0, T]` for continuous `g'`. -/
theorem card_mul_intervalIntegrable {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (T0 T : ℝ) (hT : T0 ≤ T)
    (g' : ℝ → ℝ) (hg' : ContinuousOn g' (Icc T0 T)) :
    IntervalIntegrable (fun t => g' t * ((s.filter (fun i => γ i ≤ t)).card : ℝ)) volume T0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  have : (fun t => g' t * ((s.filter (fun i => γ i ≤ t)).card : ℝ))
      = fun t => ∑ i ∈ s, (Ici (γ i)).indicator g' t := by
    funext t; rw [Finset.card_filter]; push_cast; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    simp only [indicator_apply, mem_Ici]; split_ifs <;> simp
  rw [this]
  exact integrable_finset_sum s (fun i _ =>
    ((hg'.integrableOn_Icc).mono_set Ioc_subset_Icc_self).indicator measurableSet_Ici)

/-- Lemma 4': the oscillatory head bound.  `St` is `N - M` (any function with `|St| ≤ R` on `[T1,T0]`
such that the count of ordinates in `(T1, t]` equals `M t + St t - (M T1 + St T1)`). -/
theorem osc_head_bound {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (n : ℕ) (hn : 1 ≤ n) (T1 T0 : ℝ)
    (hT1 : 2 * π ≤ T1) (hT : T1 ≤ T0) (hγ : ∀ i ∈ s, T1 < γ i ∧ γ i ≤ T0)
    (St : ℝ → ℝ)
    (hcard : ∀ t ∈ Icc T1 T0,
      ((s.filter (fun i => γ i ≤ t)).card : ℝ) = M t + St t - (M T1 + St T1))
    (hSt : ∀ t ∈ Icc T1 T0, |St t| ≤ R t) :
    2 * (M T0 - M T1 - 2 * R T0 - 2 * R T1) - 4 * Mp T0 * (T0 ^ 2 + 1 / 4) / n
        - 2 * n * R T0 * (1 / T1 - 1 / T0)
      ≤ ∑ i ∈ s, 2 * (1 - Real.cos (n * theta (γ i))) := by
  have hpi := Real.pi_gt_three
  have hT1pos : 0 < T1 := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- R is increasing on [T1, T0]
  have hRmono : ∀ t ∈ Icc T1 T0, R t ≤ R T0 := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have h1 : Real.log t ≤ Real.log T0 := Real.log_le_log ht0 ht.2
    have h2 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have h3 : Real.log (Real.log t) ≤ Real.log (Real.log T0) := Real.log_le_log h2 h1
    simp only [R]; linarith
  -- split the sum
  have hsplit : ∑ i ∈ s, 2 * (1 - Real.cos (n * theta (γ i)))
      = 2 * (s.card : ℝ) - 2 * ∑ i ∈ s, Real.cos (n * theta (γ i)) := by
    have h2 : (2 : ℝ) * (s.card : ℝ) = ∑ i ∈ s, (2 : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [Finset.mul_sum, h2, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  -- Abel summation for g = cos(nθ)
  set g' : ℝ → ℝ := fun t => n * Real.sin (n * theta t) / (t ^ 2 + 1 / 4) with hg'def
  have hg : ∀ t ∈ Icc T1 T0, HasDerivAt (fun t => Real.cos (n * theta t)) (g' t) t :=
    fun t ht => hasDerivAt_cos_ntheta n t (by linarith [ht.1])
  have hg' : ContinuousOn g' (Icc T1 T0) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hθ := continuousAt_theta t ht0
    exact (by rw [hg'def]; fun_prop (disch := positivity) : ContinuousAt g' t).continuousWithinAt
  have habel := abel_sum s γ T1 T0 hγ _ _ hg hg'
  beta_reduce at habel
  rw [← intervalIntegral.integral_of_le hT] at habel
  set c := M T1 + St T1 with hc
  have hMcont : ContinuousOn (fun t => M t - c) (Icc T1 T0) :=
    fun t ht => ((hasDerivAt_M t (by linarith [ht.1])).continuousAt.sub continuousAt_const).continuousWithinAt
  have hMpcont : ContinuousOn Mp (Icc T1 T0) :=
    fun t ht => (continuousAt_Mp t (by linarith [ht.1])).continuousWithinAt
  have hcard_int := card_mul_intervalIntegrable s γ T1 T0 hT g' hg'
  have hMc_int : IntervalIntegrable (fun t => g' t * (M t - c)) volume T1 T0 :=
    (hg'.mul hMcont).intervalIntegrable_of_Icc hT
  have hdecomp : ∫ t in T1..T0, g' t * ((s.filter (fun i => γ i ≤ t)).card : ℝ)
      = (∫ t in T1..T0, g' t * (M t - c))
        + ∫ t in T1..T0, (g' t * ((s.filter (fun i => γ i ≤ t)).card : ℝ) - g' t * (M t - c)) := by
    rw [← intervalIntegral.integral_add hMc_int (hcard_int.sub hMc_int)]
    apply intervalIntegral.integral_congr; intro t _; beta_reduce; ring
  -- integration by parts on the M-part
  have hcoscont : ContinuousOn (fun t => Real.cos (n * theta t)) (Icc T1 T0) :=
    fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hMp_int : IntervalIntegrable (fun t => Real.cos (n * theta t) * Mp t) volume T1 T0 :=
    (hcoscont.mul hMpcont).intervalIntegrable_of_Icc hT
  have hibp : ∫ t in T1..T0, (g' t * (M t - c) + Real.cos (n * theta t) * Mp t)
      = Real.cos (n * theta T0) * (M T0 - c) - Real.cos (n * theta T1) * (M T1 - c) := by
    apply intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    · rw [uIcc_of_le hT]; exact hcoscont
    · rw [uIcc_of_le hT]; exact hMcont
    · intro t ht
      rw [min_eq_left hT, max_eq_right hT] at ht
      exact hg t (Ioo_subset_Icc_self ht)
    · intro t ht
      rw [min_eq_left hT, max_eq_right hT] at ht
      exact (hasDerivAt_M t (by linarith [ht.1])).sub_const c
    · exact hg'.intervalIntegrable_of_Icc hT
    · exact hMpcont.intervalIntegrable_of_Icc hT
  rw [intervalIntegral.integral_add hMc_int hMp_int] at hibp
  -- the oscillatory integral
  have hIM := osc_integral_le n hn T1 T0 hT1 hT
  simp only [psi] at hIM
  have hIM' := abs_le.mp hIM
  -- the remainder
  have hrest : |∫ t in T1..T0, (g' t * ((s.filter (fun i => γ i ≤ t)).card : ℝ) - g' t * (M t - c))|
      ≤ n * R T0 * (1 / T1 - 1 / T0) := by
    have hinv_cont : ContinuousOn (fun t : ℝ => (n : ℝ) * R T0 * (1 / t ^ 2)) (Icc T1 T0) := by
      intro t ht
      have : 0 < t := by linarith [ht.1]
      exact (by fun_prop (disch := positivity) :
        ContinuousAt (fun t : ℝ => (n : ℝ) * R T0 * (1 / t ^ 2)) t).continuousWithinAt
    have hFTC : ∫ t in T1..T0, (n : ℝ) * R T0 * (1 / t ^ 2) = n * R T0 * (1 / T1 - 1 / T0) := by
      rw [intervalIntegral.integral_const_mul]
      have hd : ∀ t ∈ uIcc T1 T0, HasDerivAt (fun t : ℝ => -(1 / t)) (1 / t ^ 2) t := by
        intro t ht; rw [uIcc_of_le hT] at ht
        have ht0 : t ≠ 0 := (by linarith [ht.1] : (0 : ℝ) < t).ne'
        have := (hasDerivAt_inv ht0).neg
        convert this using 1
        · funext x; simp [one_div]
        · field_simp
      have hcont : ContinuousOn (fun t : ℝ => 1 / t ^ 2) (Icc T1 T0) := by
        intro t ht
        have : 0 < t := by linarith [ht.1]
        exact (by fun_prop (disch := positivity) : ContinuousAt (fun t : ℝ => 1 / t ^ 2) t).continuousWithinAt
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable_of_Icc hT)]
      ring
    rw [← hFTC, ← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hT _ (hinv_cont.intervalIntegrable_of_Icc hT)
    apply Filter.Eventually.of_forall
    intro t ht
    have ht' : t ∈ Icc T1 T0 := Ioc_subset_Icc_self ht
    have ht0 : 0 < t := by linarith [ht'.1]
    have e : g' t * ((s.filter (fun i => γ i ≤ t)).card : ℝ) - g' t * (M t - c) = g' t * St t := by
      rw [hcard t ht', hc]; ring
    rw [Real.norm_eq_abs, e, abs_mul]
    have h1 : |g' t| ≤ n * (1 / t ^ 2) := by
      rw [hg'def]
      simp only []
      rw [abs_div, abs_mul, abs_of_pos hn0, abs_of_pos (by positivity : (0:ℝ) < t ^ 2 + 1 / 4)]
      rw [div_le_iff₀ (by positivity)]
      have hs := Real.abs_sin_le_one (n * theta t)
      have h2 : (1 : ℝ) ≤ 1 / t ^ 2 * (t ^ 2 + 1 / 4) := by
        rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]; linarith
      have h3 : (n : ℝ) * |Real.sin (n * theta t)| ≤ n := by
        have := mul_le_mul_of_nonneg_left hs hn0.le; linarith
      have h4 : (n : ℝ) ≤ n * (1 / t ^ 2 * (t ^ 2 + 1 / 4)) := by
        have := mul_le_mul_of_nonneg_left h2 hn0.le; linarith
      linarith [h3, h4, (by ring : (n : ℝ) * (1 / t ^ 2 * (t ^ 2 + 1 / 4)) = n * (1 / t ^ 2) * (t ^ 2 + 1 / 4))]
    have h2 : |St t| ≤ R T0 := le_trans (hSt t ht') (hRmono t ht')
    have hRT0 : 0 ≤ R T0 := le_trans (abs_nonneg _) h2
    calc |g' t| * |St t| ≤ (n * (1 / t ^ 2)) * R T0 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = n * R T0 * (1 / t ^ 2) := by ring
  have hrest' := abs_le.mp hrest
  -- boundary terms
  have hcardT : ((s.filter (fun i => γ i ≤ T0)).card : ℝ) = s.card := by
    congr 1; apply congrArg; apply Finset.filter_true_of_mem; intro i hi; exact (hγ i hi).2
  have hcT0 := hcard T0 ⟨hT, le_rfl⟩
  rw [hcardT] at hcT0
  have hSt0 := abs_le.mp (le_trans (hSt T0 ⟨hT, le_rfl⟩) le_rfl)
  have hSt1 := abs_le.mp (hSt T1 ⟨le_rfl, hT⟩)
  have hc0 := abs_le.mp (Real.abs_cos_le_one (n * theta T0))
  have hc1 := abs_le.mp (Real.abs_cos_le_one (n * theta T1))
  have hR0 : 0 ≤ R T0 := le_trans (abs_nonneg _) (hSt T0 ⟨hT, le_rfl⟩)
  have hR1 : 0 ≤ R T1 := le_trans (abs_nonneg _) (hSt T1 ⟨le_rfl, hT⟩)
  -- |cos(nθ T0) · St T0| ≤ R T0 and the same at T1
  have hb0 : |Real.cos (n * theta T0) * St T0| ≤ R T0 := by
    rw [abs_mul]
    calc |Real.cos (n * theta T0)| * |St T0| ≤ 1 * R T0 :=
          mul_le_mul (Real.abs_cos_le_one _) (hSt T0 ⟨hT, le_rfl⟩) (abs_nonneg _) zero_le_one
      _ = R T0 := one_mul _
  have hb1 : |Real.cos (n * theta T1) * St T1| ≤ R T1 := by
    rw [abs_mul]
    calc |Real.cos (n * theta T1)| * |St T1| ≤ 1 * R T1 :=
          mul_le_mul (Real.abs_cos_le_one _) (hSt T1 ⟨le_rfl, hT⟩) (abs_nonneg _) zero_le_one
      _ = R T1 := one_mul _
  have hb0' := abs_le.mp hb0
  have hb1' := abs_le.mp hb1
  -- assemble: Σ cos = cos(nθT0)·St T0 − cos(nθT1)·St T1 + I_M − rest
  have hsum : ∑ i ∈ s, Real.cos (n * theta (γ i))
      = Real.cos (n * theta T0) * St T0 - Real.cos (n * theta T1) * St T1
        + (∫ t in T1..T0, Real.cos (n * theta t) * Mp t)
        - ∫ t in T1..T0, (g' t * ((s.filter (fun i => γ i ≤ t)).card : ℝ) - g' t * (M t - c)) := by
    rw [habel, hdecomp, hcT0]
    have : M T1 - c = -St T1 := by rw [hc]; ring
    have h2 := hibp
    rw [this] at h2
    linarith
  rw [hsplit, hsum, hcT0]
  have hdiv : 4 * Mp T0 * (T0 ^ 2 + 1 / 4) / n = 2 * (2 * (Mp T0 * (T0 ^ 2 + 1 / 4)) / n) := by ring
  rw [hdiv]
  linarith

end

end LiThreshold
