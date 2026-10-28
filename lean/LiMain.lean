/-
Final assembly of the Li-positivity theorem for a finite symmetric zero family: the counting function
`N(t) = #{i : 0 < Im ρ_i ≤ t}` with `|N - M| ≤ R` (the explicit zero-count input), the certificate inequalities
of the interval lemma, and the two end-to-end statements `li_positive_of_A1` (Lemma 4 head) and
`li_positive_of_A2` (Lemma 4' head).  The exhaustion of the full zero sum by such finite families is the
analytic input (I1) and is not formalized here.
-/
import FloorBarrier.LiSymm

open MeasureTheory Set Real

namespace LiThreshold

noncomputable section

/-- `N(t) = #{i ∈ s : 0 < Im ρ_i ≤ t}`. -/
def Ncount {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (t : ℝ) : ℝ :=
  ((s.filter (fun i => 0 < (ρ i).im ∧ (ρ i).im ≤ t)).card : ℝ)

/-- `E*(n)` of Lemma 3. -/
def Estar (n : ℕ) (c T0 : ℝ) : ℝ :=
  (n : ℝ) ^ 2 * c ^ 2 / 4 * Real.cosh (n * c / (4 * T0 ^ 2)) ^ 2 * J T0

theorem Ncount_sub {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (u t : ℝ) (hu : 0 < u) (hut : u ≤ t) :
    (((s.filter (fun i => u < (ρ i).im)).filter (fun i => (ρ i).im ≤ t)).card : ℝ)
      = Ncount s ρ t - Ncount s ρ u := by
  classical
  simp only [Ncount]
  rw [Finset.filter_filter]
  have hsplit : s.filter (fun i => 0 < (ρ i).im ∧ (ρ i).im ≤ t)
      = s.filter (fun i => 0 < (ρ i).im ∧ (ρ i).im ≤ u)
        ∪ s.filter (fun i => u < (ρ i).im ∧ (ρ i).im ≤ t) := by
    rw [← Finset.filter_or]
    apply Finset.filter_congr
    intro i _
    constructor
    · rintro ⟨h0, ht⟩
      by_cases h : (ρ i).im ≤ u
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr ⟨not_le.mp h, ht⟩
    · rintro (⟨h0, hu'⟩ | ⟨hu', ht⟩)
      · exact ⟨h0, le_trans hu' hut⟩
      · exact ⟨by linarith, ht⟩
  have hdisj : Disjoint (s.filter (fun i => 0 < (ρ i).im ∧ (ρ i).im ≤ u))
      (s.filter (fun i => u < (ρ i).im ∧ (ρ i).im ≤ t)) := by
    rw [Finset.disjoint_filter]
    intro i _ h1 h2
    linarith [h1.2, h2.1]
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  push_cast; ring

theorem filter_le_le {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (a T0 t : ℝ) (ht : t ≤ T0) :
    ((s.filter (fun i => a < (ρ i).im)).filter (fun i => (ρ i).im ≤ T0)).filter
        (fun i => (ρ i).im ≤ t)
      = (s.filter (fun i => a < (ρ i).im)).filter (fun i => (ρ i).im ≤ t) := by
  simp only [Finset.filter_filter]
  apply Finset.filter_congr
  intro i _
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h1, le_trans h3 ht⟩, h3⟩

theorem R_nonneg (t : ℝ) (ht : 2 * π ≤ t) : 0 ≤ R t := by
  have hpi := Real.pi_gt_three
  have ht0 : 0 < t := by linarith
  have he : Real.exp 1 ≤ t := by have := Real.exp_one_lt_d9; linarith
  have hlog1 : 1 ≤ Real.log t := (Real.le_log_iff_exp_le ht0).mpr he
  have := Real.log_nonneg hlog1
  simp only [R]; linarith

theorem J_nonneg (T0 : ℝ) (hT0 : 2 * π ≤ T0) : 0 ≤ J T0 := by
  have hpi := Real.pi_gt_three
  have hT0pos : 0 < T0 := by linarith
  have hR := R_nonneg T0 hT0
  have hlog : 0 ≤ Real.log (T0 / (2 * π)) := by
    apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; linarith
  have hlogT0 : 0 < Real.log T0 := Real.log_pos (by linarith)
  simp only [J]
  have h1 : 0 ≤ 2 * R T0 / T0 ^ 4 := by positivity
  have h2 : 0 ≤ (Real.log (T0 / (2 * π)) / 3 + 1 / 9) / (2 * π * T0 ^ 3) :=
    div_nonneg (by linarith) (by positivity)
  have h3 : 0 ≤ 0.10076 / (4 * T0 ^ 4) := by positivity
  have h4 : 0 ≤ 0.24460 / (4 * T0 ^ 4 * Real.log T0) := by positivity
  linarith

theorem Estar_nonneg (n : ℕ) (c T0 : ℝ) (hT0 : 2 * π ≤ T0) : 0 ≤ Estar n c T0 := by
  have := J_nonneg T0 hT0
  simp only [Estar]; positivity

theorem Estar_mono (n m : ℕ) (hnm : n ≤ m) (c T0 : ℝ) (hc : 0 ≤ c) (hT0 : 0 < T0) (hJ : 0 ≤ J T0) :
    Estar n c T0 ≤ Estar m c T0 := by
  simp only [Estar]
  have hn : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (n : ℝ) ^ 2 * c ^ 2 / 4 ≤ (m : ℝ) ^ 2 * c ^ 2 / 4 := by gcongr
  have hu : (n : ℝ) * c / (4 * T0 ^ 2) ≤ m * c / (4 * T0 ^ 2) := by gcongr
  have hu0 : 0 ≤ (n : ℝ) * c / (4 * T0 ^ 2) := by positivity
  have h2 : Real.cosh ((n : ℝ) * c / (4 * T0 ^ 2)) ≤ Real.cosh (m * c / (4 * T0 ^ 2)) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg hu0, abs_of_nonneg (by positivity)]; exact hu
  have h3 : Real.cosh ((n : ℝ) * c / (4 * T0 ^ 2)) ^ 2 ≤ Real.cosh (m * c / (4 * T0 ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (Real.cosh_pos _).le h2 2
  apply mul_le_mul_of_nonneg_right _ hJ
  exact mul_le_mul h1 h3 (by positivity) (by positivity)

/-- The tail bound in the form `4 Σ_{γ>T0} g_{nc}(γ) ≤ E*(n)`, from the counting input. -/
theorem tail_le_Estar {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (n : ℕ) (T0 T c a : ℝ)
    (hT0 : 2 * π ≤ T0) (hT : T0 ≤ T) (hc : 0 ≤ c) (haT0 : a ≤ T0)
    (himT : ∀ i ∈ s, (ρ i).im ≤ T)
    (hcount : ∀ t ∈ Icc a T, |Ncount s ρ t - M t| ≤ R t) :
    4 * ∑ i ∈ s.filter (fun i => T0 < (ρ i).im), gfun (n * c) (ρ i).im ≤ Estar n c T0 := by
  have hpi := Real.pi_gt_three
  have hT0pos : 0 < T0 := by linarith
  have htail := tail_explicit (s.filter (fun i => T0 < (ρ i).im)) (fun i => (ρ i).im) (n * c) T0 T
    (by positivity) hT0 hT
    (fun i hi => by rw [Finset.mem_filter] at hi; exact ⟨hi.2, himT i hi.1⟩)
    (fun t ht => by
      show (((s.filter (fun i => T0 < (ρ i).im)).filter (fun i => (ρ i).im ≤ t)).card : ℝ) ≤ _
      rw [Ncount_sub s ρ T0 t hT0pos ht.1]
      have h1 := abs_le.mp (hcount t ⟨le_trans haT0 ht.1, ht.2⟩)
      have h2 := abs_le.mp (hcount T0 ⟨haT0, hT⟩)
      linarith)
  simp only [Estar]
  calc 4 * ∑ i ∈ s.filter (fun i => T0 < (ρ i).im), gfun (n * c) (ρ i).im
      ≤ 4 * ((n * c) ^ 2 / 16 * Real.cosh (n * c / (4 * T0 ^ 2)) ^ 2 * J T0) :=
        mul_le_mul_of_nonneg_left htail (by norm_num)
    _ = (n : ℝ) ^ 2 * c ^ 2 / 4 * Real.cosh (n * c / (4 * T0 ^ 2)) ^ 2 * J T0 := by ring

/-- Head terms over a sub-range are at most the full head sum (all terms are `≥ 0`). -/
theorem head_subsum_le {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (n : ℕ) (a T0 : ℝ) (ha : 0 < a) :
    ∑ i ∈ (s.filter (fun i => a < (ρ i).im)).filter (fun i => (ρ i).im ≤ T0),
        2 * (1 - Real.cos (n * theta (ρ i).im))
      ≤ ∑ i ∈ s.filter (fun i => 0 < (ρ i).im ∧ (ρ i).im ≤ T0),
        2 * (1 - Real.cos (n * theta (ρ i).im)) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_filter] at hi
    rw [Finset.mem_filter]
    exact ⟨hi.1.1, by linarith [hi.1.2], hi.2⟩
  · intro i _ _
    have := Real.cos_le_one (n * theta (ρ i).im); linarith

/-- **Li positivity on an interval, small-angle certificate.**  For a finite zero family closed under
`ρ ↦ ρ̄`, `ρ ↦ 1 - ρ`, with `0 < Re ρ < 1`, `|Im ρ| ≥ 2`, all zeros of height `≤ T0` on the line, heights
`≤ T`, and counting function `N` with `|N - M| ≤ R` on `[a, T]`: if
`E*(n₂) < (4n₁²/π²)(1 - 1/(12a²))² S⁻(a)` with `n₂/π ≤ a ≤ T0`, then the partial Li sum is positive
for every `n ∈ [n₁, n₂]`. -/
theorem li_positive_of_A1 {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (σ1 σ2 : ι → ι)
    (h1s : ∀ i ∈ s, σ1 i ∈ s) (h1inv : ∀ i ∈ s, σ1 (σ1 i) = i)
    (h1ρ : ∀ i ∈ s, ρ (σ1 i) = starRingEnd ℂ (ρ i))
    (h2s : ∀ i ∈ s, σ2 i ∈ s) (h2inv : ∀ i ∈ s, σ2 (σ2 i) = i)
    (h2ρ : ∀ i ∈ s, ρ (σ2 i) = 1 - ρ i)
    (hβ : ∀ i ∈ s, 0 < (ρ i).re ∧ (ρ i).re < 1) (hγ2 : ∀ i ∈ s, 2 ≤ |(ρ i).im|)
    (T0 T c a : ℝ) (hT0 : 2 * π ≤ T0) (hT : T0 ≤ T) (hc : 1 + 2 / T0 ^ 2 ≤ c)
    (himT : ∀ i ∈ s, (ρ i).im ≤ T)
    (hline : ∀ i ∈ s, 0 < (ρ i).im → (ρ i).im ≤ T0 → (ρ i).re = 1 / 2)
    (hcount : ∀ t ∈ Icc a T, |Ncount s ρ t - M t| ≤ R t)
    (n1 n2 : ℕ) (ha1 : 1 < a) (haT0 : a ≤ T0) (hna : (n2 : ℝ) / π ≤ a)
    (hcert : Estar n2 c T0 <
      4 * (n1 : ℝ) ^ 2 / π ^ 2 * (1 - 1 / (12 * a ^ 2)) ^ 2 * Sminus a T0) :
    ∀ n : ℕ, n1 ≤ n → n ≤ n2 → 0 < ∑ i ∈ s, (1 - (1 - (ρ i)⁻¹) ^ n).re := by
  intro n hn1 hn2
  have hpi := Real.pi_gt_three
  have hT0pos : 0 < T0 := by linarith
  have hapos : 0 < a := by linarith
  have hc0 : 0 ≤ c := le_trans (by positivity : (0:ℝ) ≤ 1 + 2 / T0 ^ 2) hc
  have hmain := partial_sum_ge s ρ σ1 σ2 h1s h1inv h1ρ h2s h2inv h2ρ hβ hγ2 T0 c hT0pos hc hline n
  have htail := tail_le_Estar s ρ n T0 T c a hT0 hT hc0 haT0 himT hcount
  have hE : Estar n c T0 ≤ Estar n2 c T0 := Estar_mono n n2 hn2 c T0 hc0 hT0pos (J_nonneg T0 hT0)
  have hhead := head_bound ((s.filter (fun i => a < (ρ i).im)).filter (fun i => (ρ i).im ≤ T0))
    (fun i => (ρ i).im) n a T0 ha1 haT0
    (by
      have h : (n : ℝ) ≤ n2 := by exact_mod_cast hn2
      have h' : (n : ℝ) / π ≤ n2 / π := by gcongr
      exact le_trans h' hna)
    (fun i hi => by rw [Finset.mem_filter, Finset.mem_filter] at hi; exact ⟨hi.1.2, hi.2⟩)
    (fun t ht => by
      show M t - R t - (M a + R a) ≤
        ((((s.filter (fun i => a < (ρ i).im)).filter (fun i => (ρ i).im ≤ T0)).filter
          (fun i => (ρ i).im ≤ t)).card : ℝ)
      rw [filter_le_le s ρ a T0 t ht.2, Ncount_sub s ρ a t hapos ht.1]
      have h1 := abs_le.mp (hcount t ⟨ht.1, le_trans ht.2 hT⟩)
      have h2 := abs_le.mp (hcount a ⟨le_rfl, le_trans haT0 hT⟩)
      linarith)
  have hsub := head_subsum_le s ρ n a T0 hapos
  have hS : 0 ≤ Sminus a T0 := by
    have hE0 := Estar_nonneg n2 c T0 hT0
    by_contra hneg
    push_neg at hneg
    have : 4 * (n1 : ℝ) ^ 2 / π ^ 2 * (1 - 1 / (12 * a ^ 2)) ^ 2 * Sminus a T0 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg.le
    linarith
  have hA : 4 * (n1 : ℝ) ^ 2 / π ^ 2 * (1 - 1 / (12 * a ^ 2)) ^ 2 * Sminus a T0
      ≤ 4 * (n : ℝ) ^ 2 / π ^ 2 * (1 - 1 / (12 * a ^ 2)) ^ 2 * Sminus a T0 := by
    have hn : (n1 : ℝ) ≤ n := by exact_mod_cast hn1
    have : 4 * (n1 : ℝ) ^ 2 / π ^ 2 ≤ 4 * (n : ℝ) ^ 2 / π ^ 2 := by gcongr
    apply mul_le_mul_of_nonneg_right _ hS
    apply mul_le_mul_of_nonneg_right this (by positivity)
  linarith [hmain, hhead, hsub, hE, htail, hA, hcert]

/-- **Li positivity on an interval, oscillatory certificate.**  Same setting, with the counting input on
`[T1, T]` and the Lemma 4' bound: if
`E*(n₂) < 2[M(T0) - M(T1) - 2R(T0) - 2R(T1)] - 4M'(T0)(T0² + 1/4)/n₁ - 2 n₂ R(T0)(1/T1 - 1/T0)` with
`2π ≤ T1 ≤ T0` and `n₁ ≥ 1`, then the partial Li sum is positive for every `n ∈ [n₁, n₂]`. -/
theorem li_positive_of_A2 {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (σ1 σ2 : ι → ι)
    (h1s : ∀ i ∈ s, σ1 i ∈ s) (h1inv : ∀ i ∈ s, σ1 (σ1 i) = i)
    (h1ρ : ∀ i ∈ s, ρ (σ1 i) = starRingEnd ℂ (ρ i))
    (h2s : ∀ i ∈ s, σ2 i ∈ s) (h2inv : ∀ i ∈ s, σ2 (σ2 i) = i)
    (h2ρ : ∀ i ∈ s, ρ (σ2 i) = 1 - ρ i)
    (hβ : ∀ i ∈ s, 0 < (ρ i).re ∧ (ρ i).re < 1) (hγ2 : ∀ i ∈ s, 2 ≤ |(ρ i).im|)
    (T0 T c T1 : ℝ) (hT0 : 2 * π ≤ T0) (hT : T0 ≤ T) (hc : 1 + 2 / T0 ^ 2 ≤ c)
    (himT : ∀ i ∈ s, (ρ i).im ≤ T)
    (hline : ∀ i ∈ s, 0 < (ρ i).im → (ρ i).im ≤ T0 → (ρ i).re = 1 / 2)
    (hcount : ∀ t ∈ Icc T1 T, |Ncount s ρ t - M t| ≤ R t)
    (n1 n2 : ℕ) (hn1 : 1 ≤ n1) (hT1 : 2 * π ≤ T1) (hT1T0 : T1 ≤ T0)
    (hcert : Estar n2 c T0 <
      2 * (M T0 - M T1 - 2 * R T0 - 2 * R T1) - 4 * Mp T0 * (T0 ^ 2 + 1 / 4) / n1
        - 2 * n2 * R T0 * (1 / T1 - 1 / T0)) :
    ∀ n : ℕ, n1 ≤ n → n ≤ n2 → 0 < ∑ i ∈ s, (1 - (1 - (ρ i)⁻¹) ^ n).re := by
  intro n hn1' hn2
  have hpi := Real.pi_gt_three
  have hT0pos : 0 < T0 := by linarith
  have hT1pos : 0 < T1 := by linarith
  have hc0 : 0 ≤ c := le_trans (by positivity : (0:ℝ) ≤ 1 + 2 / T0 ^ 2) hc
  have hmain := partial_sum_ge s ρ σ1 σ2 h1s h1inv h1ρ h2s h2inv h2ρ hβ hγ2 T0 c hT0pos hc hline n
  have htail := tail_le_Estar s ρ n T0 T c T1 hT0 hT hc0 hT1T0 himT hcount
  have hE : Estar n c T0 ≤ Estar n2 c T0 := Estar_mono n n2 hn2 c T0 hc0 hT0pos (J_nonneg T0 hT0)
  have hn : 1 ≤ n := le_trans hn1 hn1'
  have hhead := osc_head_bound ((s.filter (fun i => T1 < (ρ i).im)).filter (fun i => (ρ i).im ≤ T0))
    (fun i => (ρ i).im) n hn T1 T0 hT1 hT1T0
    (fun i hi => by rw [Finset.mem_filter, Finset.mem_filter] at hi; exact ⟨hi.1.2, hi.2⟩)
    (fun t => Ncount s ρ t - M t)
    (fun t ht => by
      show ((((s.filter (fun i => T1 < (ρ i).im)).filter (fun i => (ρ i).im ≤ T0)).filter
          (fun i => (ρ i).im ≤ t)).card : ℝ) = _
      rw [filter_le_le s ρ T1 T0 t ht.2, Ncount_sub s ρ T1 t hT1pos ht.1]
      ring)
    (fun t ht => hcount t ⟨ht.1, le_trans ht.2 hT⟩)
  have hsub := head_subsum_le s ρ n T1 T0 hT1pos
  -- monotonicity of A' in n
  have hpsi : 0 ≤ Mp T0 * (T0 ^ 2 + 1 / 4) := mul_nonneg (Mp_nonneg T0 hT0) (by positivity)
  have hR0 := R_nonneg T0 hT0
  have hinv : 0 ≤ 1 / T1 - 1 / T0 := by
    have := one_div_le_one_div_of_le hT1pos hT1T0; linarith
  have hn1r : (n1 : ℝ) ≤ n := by exact_mod_cast hn1'
  have hn2r : (n : ℝ) ≤ n2 := by exact_mod_cast hn2
  have hn1pos : (0 : ℝ) < n1 := by exact_mod_cast hn1
  have hA1 : 4 * Mp T0 * (T0 ^ 2 + 1 / 4) / n ≤ 4 * Mp T0 * (T0 ^ 2 + 1 / 4) / n1 := by
    have : 0 ≤ 4 * Mp T0 * (T0 ^ 2 + 1 / 4) := by linarith
    exact div_le_div_of_nonneg_left this hn1pos hn1r
  have hA2 : 2 * (n : ℝ) * R T0 * (1 / T1 - 1 / T0) ≤ 2 * n2 * R T0 * (1 / T1 - 1 / T0) := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn2r hR0) hinv
    linarith
  linarith [hmain, hhead, hsub, hE, htail, hA1, hA2, hcert]

end

end LiThreshold
