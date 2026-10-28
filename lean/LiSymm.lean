/-
Reduction of the symmetric zero sum to ordinates `γ > 0`: on-line pairs give `2(1 - cos nθ_γ)`,
off-line quadruples are bounded below by `-4 g_{nc}(γ)`.  The zero set is a finite family `ρ : ι → ℂ`
indexed by `s : Finset ι`, closed under the two involutions `ρ ↦ conj ρ` and `ρ ↦ 1 - ρ` (given as maps
`σ1 σ2 : ι → ι` on the index set, so multiplicities are respected).
-/
import FloorBarrier.LiOsc

open MeasureTheory Set Real

namespace LiThreshold

noncomputable section

/-- The orbit sum `Σ_{σ ∈ V} (1 - (1 - 1/σρ)^n)` in real form (Lemma 2). -/
def Forb (n : ℕ) (ρ : ℂ) : ℝ := 4 - 2 * ((1 - ρ⁻¹) ^ n).re - 2 * ((1 - ρ⁻¹)⁻¹ ^ n).re

theorem cos_theta (γ : ℝ) (hγ : 0 < γ) :
    Real.cos (theta γ) = (γ ^ 2 - 1 / 4) / (γ ^ 2 + 1 / 4) := by
  simp only [theta]
  rw [Real.cos_two_mul, Real.cos_sq_arctan]
  field_simp
  ring

theorem sin_theta (γ : ℝ) (hγ : 0 < γ) : Real.sin (theta γ) = γ / (γ ^ 2 + 1 / 4) := by
  simp only [theta]
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  have h : (0:ℝ) < 1 + (1 / (2 * γ)) ^ 2 := by positivity
  have e : 1 / (2 * γ) / √(1 + (1 / (2 * γ)) ^ 2) * (1 / √(1 + (1 / (2 * γ)) ^ 2))
      = 1 / (2 * γ) / (1 + (1 / (2 * γ)) ^ 2) := by
    rw [div_mul_div_comm, mul_one, Real.mul_self_sqrt h.le]
  rw [mul_assoc, e]
  field_simp
  ring

/-- On the line, `1 - 1/ρ = e^{iθ_γ}` with `γ = Im ρ > 0`. -/
theorem online_w (ρ : ℂ) (hre : ρ.re = 1 / 2) (him : 0 < ρ.im) :
    1 - ρ⁻¹ = Complex.exp ((theta ρ.im : ℂ) * Complex.I) := by
  have hρ : ρ ≠ 0 := by intro h; rw [h] at him; simp at him
  have key : ρ * Complex.exp ((theta ρ.im : ℂ) * Complex.I) = ρ - 1 := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im, cos_theta _ him, sin_theta _ him, hre]
      field_simp
      ring
    · simp only [Complex.mul_im, Complex.sub_im, Complex.one_im, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im, cos_theta _ him, sin_theta _ him, hre]
      field_simp
      ring
  have : 1 - ρ⁻¹ = (ρ - 1) / ρ := by field_simp
  rw [this, ← key, mul_div_cancel_left₀ _ hρ]

/-- Lemma 1: on-line orbit sum. -/
theorem Forb_online (n : ℕ) (ρ : ℂ) (hre : ρ.re = 1 / 2) (him : 0 < ρ.im) :
    Forb n ρ = 4 - 4 * Real.cos (n * theta ρ.im) := by
  simp only [Forb]
  rw [online_w ρ hre him, ← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have e1 : (n : ℂ) * ((theta ρ.im : ℂ) * Complex.I) = ((n * theta ρ.im : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have e2 : (n : ℂ) * -((theta ρ.im : ℂ) * Complex.I) = ((-(n * theta ρ.im) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e1, e2, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  ring

/-- Lemma 2: off-line orbit sum, `≥ -8 g_{nc}(γ)` when `c ≥ 1 + 2/γ²`. -/
theorem Forb_offline (n : ℕ) (ρ : ℂ) (c : ℝ) (hβ0 : 0 < ρ.re) (hβ1 : ρ.re < 1) (hγ : 2 ≤ |ρ.im|)
    (hc : 1 + 2 / ρ.im ^ 2 ≤ c) : -8 * gfun (n * c) ρ.im ≤ Forb n ρ := by
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hβ1; simp at hβ1
  have hw : (1 - ρ⁻¹) ≠ 0 := by
    intro h
    apply hρ1
    have : ρ⁻¹ = 1 := by linear_combination -h
    exact inv_eq_one.mp this
  have h1 := quad_sum_ge (1 - ρ⁻¹) hw n
  have h2 := four_sub_four_cosh (n * Real.log ‖1 - ρ⁻¹‖)
  have hδ := delta_bound ρ hβ0 hβ1 hγ
  have hγ2 : 4 ≤ ρ.im ^ 2 := by nlinarith [sq_abs ρ.im, abs_nonneg ρ.im]
  have hδ' : |Real.log ‖1 - ρ⁻¹‖| ≤ c / (2 * ρ.im ^ 2) := by
    refine le_trans hδ ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : |1 - 2 * ρ.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    linarith
  have hy : |n * Real.log ‖1 - ρ⁻¹‖ / 2| ≤ n * c / (4 * ρ.im ^ 2) := by
    rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ n), abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc (n : ℝ) * |Real.log ‖1 - ρ⁻¹‖| / 2 ≤ n * (c / (2 * ρ.im ^ 2)) / 2 := by gcongr
      _ = n * c / (4 * ρ.im ^ 2) := by field_simp; ring
  have hsq : Real.sinh (n * Real.log ‖1 - ρ⁻¹‖ / 2) ^ 2 ≤ Real.sinh (n * c / (4 * ρ.im ^ 2)) ^ 2 := by
    rw [← sq_abs (Real.sinh _), Real.abs_sinh]
    have h0 : 0 ≤ Real.sinh |n * Real.log ‖1 - ρ⁻¹‖ / 2| := Real.sinh_nonneg_iff.mpr (abs_nonneg _)
    have hle : Real.sinh |n * Real.log ‖1 - ρ⁻¹‖ / 2| ≤ Real.sinh (n * c / (4 * ρ.im ^ 2)) :=
      Real.sinh_le_sinh.mpr hy
    nlinarith
  simp only [Forb, gfun]
  linarith

theorem sum_reindex {ι : Type*} (s : Finset ι) (σ : ι → ι) (hs : ∀ i ∈ s, σ i ∈ s)
    (hinv : ∀ i ∈ s, σ (σ i) = i) (f : ι → ℂ) :
    ∑ i ∈ s, f (σ i) = ∑ i ∈ s, f i := by
  apply Finset.sum_nbij' σ σ hs hs hinv hinv
  intro i _; rfl

theorem w_one_sub (z : ℂ) (h0 : z ≠ 0) (h1 : z ≠ 1) : 1 - (1 - z)⁻¹ = (1 - z⁻¹)⁻¹ := by
  have : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have : (1 : ℂ) - z⁻¹ ≠ 0 := by
    intro h; apply h1
    have : z⁻¹ = 1 := by linear_combination -h
    exact inv_eq_one.mp this
  field_simp
  ring

/-- The V-symmetric sum equals one quarter of the sum of orbit sums. -/
theorem symmetric_sum_eq {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (σ1 σ2 : ι → ι)
    (h1s : ∀ i ∈ s, σ1 i ∈ s) (h1inv : ∀ i ∈ s, σ1 (σ1 i) = i)
    (h1ρ : ∀ i ∈ s, ρ (σ1 i) = starRingEnd ℂ (ρ i))
    (h2s : ∀ i ∈ s, σ2 i ∈ s) (h2inv : ∀ i ∈ s, σ2 (σ2 i) = i)
    (h2ρ : ∀ i ∈ s, ρ (σ2 i) = 1 - ρ i)
    (hρ0 : ∀ i ∈ s, ρ i ≠ 0) (hρ1 : ∀ i ∈ s, ρ i ≠ 1) (n : ℕ) :
    ∑ i ∈ s, (1 - (1 - (ρ i)⁻¹) ^ n).re = (1 / 4) * ∑ i ∈ s, Forb n (ρ i) := by
  set f : ℂ → ℂ := fun z => 1 - (1 - z⁻¹) ^ n with hf
  have e1 : ∑ i ∈ s, f (ρ (σ1 i)) = ∑ i ∈ s, f (ρ i) := sum_reindex s σ1 h1s h1inv (fun i => f (ρ i))
  have e2 : ∑ i ∈ s, f (ρ (σ2 i)) = ∑ i ∈ s, f (ρ i) := sum_reindex s σ2 h2s h2inv (fun i => f (ρ i))
  have h12s : ∀ i ∈ s, σ1 (σ2 i) ∈ s := fun i hi => h1s _ (h2s i hi)
  have h21s : ∀ i ∈ s, σ2 (σ1 i) ∈ s := fun i hi => h2s _ (h1s i hi)
  have e3 : ∑ i ∈ s, f (ρ (σ1 (σ2 i))) = ∑ i ∈ s, f (ρ i) := by
    apply Finset.sum_nbij' (fun i => σ1 (σ2 i)) (fun i => σ2 (σ1 i)) h12s h21s
    · intro i hi; rw [h1inv _ (h2s i hi), h2inv i hi]
    · intro i hi; rw [h2inv _ (h1s i hi), h1inv i hi]
    · intro i _; rfl
  have hpt : ∀ i ∈ s, f (ρ i) + f (ρ (σ1 i)) + f (ρ (σ2 i)) + f (ρ (σ1 (σ2 i)))
      = (Forb n (ρ i) : ℂ) := by
    intro i hi
    have hw1 : 1 - (ρ (σ1 i))⁻¹ = starRingEnd ℂ (1 - (ρ i)⁻¹) := by
      rw [h1ρ i hi, map_sub, map_one, map_inv₀]
    have hw2 : 1 - (ρ (σ2 i))⁻¹ = (1 - (ρ i)⁻¹)⁻¹ := by
      rw [h2ρ i hi]; exact w_one_sub _ (hρ0 i hi) (hρ1 i hi)
    have hw3 : 1 - (ρ (σ1 (σ2 i)))⁻¹ = (starRingEnd ℂ (1 - (ρ i)⁻¹))⁻¹ := by
      rw [h1ρ _ (h2s i hi), h2ρ i hi]
      have e : 1 - (starRingEnd ℂ (1 - ρ i))⁻¹ = starRingEnd ℂ (1 - (1 - ρ i)⁻¹) := by
        simp
      rw [e, w_one_sub _ (hρ0 i hi) (hρ1 i hi), map_inv₀]
    simp only [hf, Forb]
    rw [hw1, hw2, hw3]
    exact quad_sum_eq (1 - (ρ i)⁻¹) n
  have hsum : ∑ i ∈ s, (f (ρ i) + f (ρ (σ1 i)) + f (ρ (σ2 i)) + f (ρ (σ1 (σ2 i))))
      = ∑ i ∈ s, (Forb n (ρ i) : ℂ) := Finset.sum_congr rfl hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e2, e3] at hsum
  have := congrArg Complex.re hsum
  simp only [Complex.add_re, Complex.re_sum, Complex.ofReal_re] at this
  simp only [hf] at this
  linarith

theorem Forb_conj (n : ℕ) (ρ : ℂ) : Forb n (starRingEnd ℂ ρ) = Forb n ρ := by
  simp only [Forb]
  have : 1 - (starRingEnd ℂ ρ)⁻¹ = starRingEnd ℂ (1 - ρ⁻¹) := by rw [map_sub, map_one, map_inv₀]
  rw [this, ← map_inv₀, ← map_pow, ← map_pow, Complex.conj_re, Complex.conj_re]

/-- Conjugation symmetry halves the sum to ordinates `> 0`. -/
theorem symmetric_sum_pos {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (σ1 : ι → ι)
    (h1s : ∀ i ∈ s, σ1 i ∈ s) (h1inv : ∀ i ∈ s, σ1 (σ1 i) = i)
    (h1ρ : ∀ i ∈ s, ρ (σ1 i) = starRingEnd ℂ (ρ i)) (him : ∀ i ∈ s, (ρ i).im ≠ 0) (n : ℕ) :
    ∑ i ∈ s, Forb n (ρ i) = 2 * ∑ i ∈ s.filter (fun i => 0 < (ρ i).im), Forb n (ρ i) := by
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i => 0 < (ρ i).im)]
  have : ∑ i ∈ s.filter (fun i => ¬ 0 < (ρ i).im), Forb n (ρ i)
      = ∑ i ∈ s.filter (fun i => 0 < (ρ i).im), Forb n (ρ i) := by
    apply Finset.sum_nbij' σ1 σ1
    · intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨h1s i hi.1, ?_⟩
      rw [h1ρ i hi.1, Complex.conj_im]
      have h1 : (ρ i).im ≤ 0 := not_lt.mp hi.2
      have h2 : (ρ i).im < 0 := lt_of_le_of_ne h1 (him i hi.1)
      linarith
    · intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨h1s i hi.1, ?_⟩
      rw [h1ρ i hi.1, Complex.conj_im]
      linarith [hi.2]
    · intro i hi; exact h1inv i (Finset.mem_filter.mp hi).1
    · intro i hi; exact h1inv i (Finset.mem_filter.mp hi).1
    · intro i hi; rw [h1ρ i (Finset.mem_filter.mp hi).1, Forb_conj]
  rw [this]; ring

/-- The partial Li sum over a V-symmetric finite zero set is bounded below by the head terms
(on-line pairs, `0 < γ ≤ T0`) minus `4 Σ_{γ > T0} g_{nc}(γ)`. -/
theorem partial_sum_ge {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (σ1 σ2 : ι → ι)
    (h1s : ∀ i ∈ s, σ1 i ∈ s) (h1inv : ∀ i ∈ s, σ1 (σ1 i) = i)
    (h1ρ : ∀ i ∈ s, ρ (σ1 i) = starRingEnd ℂ (ρ i))
    (h2s : ∀ i ∈ s, σ2 i ∈ s) (h2inv : ∀ i ∈ s, σ2 (σ2 i) = i)
    (h2ρ : ∀ i ∈ s, ρ (σ2 i) = 1 - ρ i)
    (hβ : ∀ i ∈ s, 0 < (ρ i).re ∧ (ρ i).re < 1) (hγ2 : ∀ i ∈ s, 2 ≤ |(ρ i).im|)
    (T0 c : ℝ) (hT0 : 0 < T0) (hc : 1 + 2 / T0 ^ 2 ≤ c)
    (hline : ∀ i ∈ s, 0 < (ρ i).im → (ρ i).im ≤ T0 → (ρ i).re = 1 / 2) (n : ℕ) :
    (∑ i ∈ s.filter (fun i => 0 < (ρ i).im ∧ (ρ i).im ≤ T0), 2 * (1 - Real.cos (n * theta (ρ i).im)))
      - 4 * ∑ i ∈ s.filter (fun i => T0 < (ρ i).im), gfun (n * c) (ρ i).im
      ≤ ∑ i ∈ s, (1 - (1 - (ρ i)⁻¹) ^ n).re := by
  have hρ0 : ∀ i ∈ s, ρ i ≠ 0 := fun i hi h => by
    have := (hβ i hi).1; rw [h] at this; simp at this
  have hρ1 : ∀ i ∈ s, ρ i ≠ 1 := fun i hi h => by
    have := (hβ i hi).2; rw [h] at this; simp at this
  have him : ∀ i ∈ s, (ρ i).im ≠ 0 := fun i hi h => by
    have := hγ2 i hi; rw [h, abs_zero] at this; linarith
  rw [symmetric_sum_eq s ρ σ1 σ2 h1s h1inv h1ρ h2s h2inv h2ρ hρ0 hρ1 n,
    symmetric_sum_pos s ρ σ1 h1s h1inv h1ρ him n]
  rw [← Finset.sum_filter_add_sum_filter_not (s.filter (fun i => 0 < (ρ i).im)) (fun i => (ρ i).im ≤ T0)]
  have hA : (s.filter (fun i => 0 < (ρ i).im)).filter (fun i => (ρ i).im ≤ T0)
      = s.filter (fun i => 0 < (ρ i).im ∧ (ρ i).im ≤ T0) := by
    rw [Finset.filter_filter]
  have hB : (s.filter (fun i => 0 < (ρ i).im)).filter (fun i => ¬ (ρ i).im ≤ T0)
      = s.filter (fun i => T0 < (ρ i).im) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro i _
    constructor
    · rintro ⟨_, h⟩; exact not_le.mp h
    · intro h; exact ⟨by linarith, not_le.mpr h⟩
  rw [hA, hB]
  have hon : ∀ i ∈ s.filter (fun i => 0 < (ρ i).im ∧ (ρ i).im ≤ T0),
      Forb n (ρ i) = 4 - 4 * Real.cos (n * theta (ρ i).im) := by
    intro i hi; rw [Finset.mem_filter] at hi
    exact Forb_online n (ρ i) (hline i hi.1 hi.2.1 hi.2.2) hi.2.1
  have hoff : ∀ i ∈ s.filter (fun i => T0 < (ρ i).im), -8 * gfun (n * c) (ρ i).im ≤ Forb n (ρ i) := by
    intro i hi; rw [Finset.mem_filter] at hi
    apply Forb_offline n (ρ i) c (hβ i hi.1).1 (hβ i hi.1).2 (hγ2 i hi.1)
    have : 2 / (ρ i).im ^ 2 ≤ 2 / T0 ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith [hi.2])
    linarith
  rw [Finset.sum_congr rfl hon]
  have hsum := Finset.sum_le_sum hoff
  rw [← Finset.mul_sum] at hsum
  have e : ∑ i ∈ s.filter (fun i => 0 < (ρ i).im ∧ (ρ i).im ≤ T0), (4 - 4 * Real.cos (n * theta (ρ i).im))
      = 2 * ∑ i ∈ s.filter (fun i => 0 < (ρ i).im ∧ (ρ i).im ≤ T0),
          2 * (1 - Real.cos (n * theta (ρ i).im)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [e]
  linarith

end

end LiThreshold
