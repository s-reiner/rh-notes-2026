/-
Abel summation over a finite family of ordinates: the Lean form of the Stieltjes integration by parts
used in Lemmas 3, 4, 4' of the Li-positivity note. Everything is over the set `Ioc T0 T`.
-/
import Mathlib

open MeasureTheory Set

namespace LiThreshold

/-- Per-term identity: for `T0 < a ≤ T` and `g` differentiable on `[T0,T]` with continuous derivative `g'`,
`g a = g T - ∫_{Ioc T0 T} (Ici a).indicator g'`. -/
theorem term_identity (T0 T a : ℝ) (ha : T0 < a) (haT : a ≤ T)
    (g g' : ℝ → ℝ) (hg : ∀ t ∈ Icc T0 T, HasDerivAt g (g' t) t)
    (hg' : ContinuousOn g' (Icc T0 T)) :
    g a = g T - ∫ t in Ioc T0 T, (Ici a).indicator g' t := by
  have hIcc : Icc a T ⊆ Icc T0 T := Icc_subset_Icc ha.le le_rfl
  have hftc : ∫ t in a..T, g' t = g T - g a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht; exact hg t (hIcc (by rwa [uIcc_of_le haT] at ht))
    · exact (hg'.mono hIcc).intervalIntegrable_of_Icc haT
  have hset : Ici a ∩ Ioc T0 T = Icc a T := by
    ext t; simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]; constructor
    · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, lt_of_lt_of_le ha h1, h2⟩
  have hind : ∫ t in Ioc T0 T, (Ici a).indicator g' t = ∫ t in a..T, g' t := by
    rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici, hset,
      integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le haT]
  rw [hind, hftc]; ring

/-- Abel summation: for ordinates `γ i ∈ (T0, T]`, `i ∈ s`,
`∑ g(γ i) = |s| g(T) - ∫_{Ioc T0 T} g'(t) · #{i ∈ s : γ i ≤ t} dt`. -/
theorem abel_sum {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (T0 T : ℝ)
    (hγ : ∀ i ∈ s, T0 < γ i ∧ γ i ≤ T)
    (g g' : ℝ → ℝ) (hg : ∀ t ∈ Icc T0 T, HasDerivAt g (g' t) t)
    (hg' : ContinuousOn g' (Icc T0 T)) :
    ∑ i ∈ s, g (γ i)
      = (s.card : ℝ) * g T - ∫ t in Ioc T0 T, g' t * ((s.filter (fun i => γ i ≤ t)).card : ℝ) := by
  have hterm : ∀ i ∈ s, g (γ i) = g T - ∫ t in Ioc T0 T, (Ici (γ i)).indicator g' t :=
    fun i hi => term_identity T0 T (γ i) (hγ i hi).1 (hγ i hi).2 g g' hg hg'
  have hint : ∀ i ∈ s, Integrable (fun t => (Ici (γ i)).indicator g' t) (volume.restrict (Ioc T0 T)) := by
    intro i hi
    have : IntegrableOn g' (Ioc T0 T) :=
      (hg'.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    exact this.indicator measurableSet_Ici
  have hsum_ind : ∀ t, ∑ i ∈ s, (Ici (γ i)).indicator g' t
      = g' t * ((s.filter (fun i => γ i ≤ t)).card : ℝ) := by
    intro t
    rw [Finset.card_filter]; push_cast; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    simp only [indicator_apply, mem_Ici]; split_ifs <;> simp
  calc ∑ i ∈ s, g (γ i) = ∑ i ∈ s, (g T - ∫ t in Ioc T0 T, (Ici (γ i)).indicator g' t) :=
        Finset.sum_congr rfl hterm
    _ = (s.card : ℝ) * g T - ∑ i ∈ s, ∫ t in Ioc T0 T, (Ici (γ i)).indicator g' t := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    _ = (s.card : ℝ) * g T - ∫ t in Ioc T0 T, ∑ i ∈ s, (Ici (γ i)).indicator g' t := by
        rw [integral_finset_sum s hint]
    _ = _ := by simp_rw [hsum_ind]

/-- Tail inequality (the content of Lemma 3's Stieltjes steps): if `g ≥ 0` is decreasing (`g' ≤ 0`) on
`[T0,T]`, the ordinates lie in `(T0,T]`, and the counting function is bounded by `Nup` with `Nup` of class `C¹`
(`Nup' ` its derivative), then `∑ g(γ i) ≤ g(T0) Nup(T0) + ∫_{T0}^{T} g Nup'`. -/
theorem tail_sum_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (T0 T : ℝ) (hT : T0 ≤ T)
    (hγ : ∀ i ∈ s, T0 < γ i ∧ γ i ≤ T)
    (g g' : ℝ → ℝ) (hg : ∀ t ∈ Icc T0 T, HasDerivAt g (g' t) t)
    (hg' : ContinuousOn g' (Icc T0 T))
    (hg0 : ∀ t ∈ Icc T0 T, 0 ≤ g t) (hgdec : ∀ t ∈ Icc T0 T, g' t ≤ 0)
    (Nup Nup' : ℝ → ℝ) (hN : ∀ t ∈ Icc T0 T, HasDerivAt Nup (Nup' t) t)
    (hN' : ContinuousOn Nup' (Icc T0 T))
    (hcount : ∀ t ∈ Icc T0 T, ((s.filter (fun i => γ i ≤ t)).card : ℝ) ≤ Nup t) :
    ∑ i ∈ s, g (γ i) ≤ g T0 * Nup T0 + ∫ t in T0..T, g t * Nup' t := by
  rw [abel_sum s γ T0 T hγ g g' hg hg']
  -- continuity facts
  have hgc : ContinuousOn g (Icc T0 T) := fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hNc : ContinuousOn Nup (Icc T0 T) := fun t ht => (hN t ht).continuousAt.continuousWithinAt
  -- step 1: ∫ g' · card ≥ ∫ g' · Nup  (since g' ≤ 0 and card ≤ Nup)
  have hcard_int : IntegrableOn (fun t => g' t * ((s.filter (fun i => γ i ≤ t)).card : ℝ)) (Ioc T0 T) := by
    -- it equals the finite sum of indicator functions (see abel_sum); reuse integrability of each
    have : (fun t => g' t * ((s.filter (fun i => γ i ≤ t)).card : ℝ))
        = fun t => ∑ i ∈ s, (Ici (γ i)).indicator g' t := by
      funext t; rw [Finset.card_filter]; push_cast; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      simp only [indicator_apply, mem_Ici]; split_ifs <;> simp
    rw [this]
    exact integrable_finset_sum s (fun i _ =>
      ((hg'.integrableOn_Icc).mono_set Ioc_subset_Icc_self).indicator measurableSet_Ici)
  have hgN_int : IntegrableOn (fun t => g' t * Nup t) (Ioc T0 T) :=
    ((hg'.mul hNc).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hstep1 : ∫ t in Ioc T0 T, g' t * Nup t ≤ ∫ t in Ioc T0 T, g' t * ((s.filter (fun i => γ i ≤ t)).card : ℝ) := by
    apply setIntegral_mono_on hgN_int hcard_int measurableSet_Ioc
    intro t ht
    have ht' : t ∈ Icc T0 T := Ioc_subset_Icc_self ht
    have := hgdec t ht'
    have := hcount t ht'
    nlinarith
  -- step 2: integration by parts for ∫ g' Nup
  have hibp : ∫ t in T0..T, (g' t * Nup t + g t * Nup' t) = g T * Nup T - g T0 * Nup T0 := by
    apply intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    · rwa [uIcc_of_le hT]
    · rwa [uIcc_of_le hT]
    · intro t ht
      rw [min_eq_left hT, max_eq_right hT] at ht
      exact hg t (Ioo_subset_Icc_self ht)
    · intro t ht
      rw [min_eq_left hT, max_eq_right hT] at ht
      exact hN t (Ioo_subset_Icc_self ht)
    · exact hg'.intervalIntegrable_of_Icc hT
    · exact hN'.intervalIntegrable_of_Icc hT
  have hsplit : ∫ t in T0..T, (g' t * Nup t + g t * Nup' t)
      = (∫ t in T0..T, g' t * Nup t) + ∫ t in T0..T, g t * Nup' t := by
    apply intervalIntegral.integral_add
    · exact (hg'.mul hNc).intervalIntegrable_of_Icc hT
    · exact (hgc.mul hN').intervalIntegrable_of_Icc hT
  -- step 3: card(T) g(T) ≤ Nup(T) g(T)
  have hcardT : ((s.filter (fun i => γ i ≤ T)).card : ℝ) = s.card := by
    congr 1; apply congrArg; apply Finset.filter_true_of_mem; intro i hi; exact (hγ i hi).2
  have hgT : 0 ≤ g T := hg0 T ⟨hT, le_rfl⟩
  have hNT : (s.card : ℝ) ≤ Nup T := by rw [← hcardT]; exact hcount T ⟨hT, le_rfl⟩
  -- assemble
  have e1 : ∫ t in Ioc T0 T, g' t * Nup t = ∫ t in T0..T, g' t * Nup t := (intervalIntegral.integral_of_le hT).symm
  rw [e1] at hstep1
  have := mul_le_mul_of_nonneg_right hNT hgT
  nlinarith [hstep1, hibp, hsplit]

end LiThreshold
