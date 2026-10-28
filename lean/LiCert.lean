/-
Rational enclosures for the Li certificate chain (stage 3).
log 2, log 3, log 5, log π and log log T0 are enclosed via Mathlib's series bound
`Real.abs_log_sub_add_sum_range_le`; π via `Real.pi_gt_d20`/`Real.pi_lt_d20`; 1/(2π); the tail constant
J(T0) for T0 = 3·10¹²; and the crude bound cosh x ≤ 2 for |x| ≤ 1.  The per-interval certificates are
generated in `LiChain.lean`.
-/
import FloorBarrier.LiMain

open Real Finset

namespace LiThreshold.Cert

theorem log_bounds_of (r : ℝ) (n : ℕ) (h : |1 - r| < 1) :
    -(∑ i ∈ range n, (1 - r) ^ (i + 1) / (i + 1)) - |1 - r| ^ (n + 1) / (1 - |1 - r|) ≤ log r ∧
    log r ≤ -(∑ i ∈ range n, (1 - r) ^ (i + 1) / (i + 1)) + |1 - r| ^ (n + 1) / (1 - |1 - r|) := by
  have h' := Real.abs_log_sub_add_sum_range_le h n
  rw [sub_sub_cancel] at h'
  have := abs_le.mp h'
  constructor <;> linarith [this.1, this.2]

theorem log2_b : (0.693147180559944403146475 : ℝ) ≤ log 2 ∧ log 2 ≤ 0.693147180559946181503315 := by
  obtain ⟨h1, h2⟩ := log_bounds_of (1 / 2) 50 (by norm_num [abs_of_pos])
  have e : log (1 / 2 : ℝ) = -log 2 := by rw [one_div, Real.log_inv]
  rw [e] at h1 h2
  norm_num [Finset.sum_range_succ, abs_of_pos] at h1 h2
  constructor <;> linarith

theorem log3_b : (1.098612288668107593043818 : ℝ) ≤ log 3 ∧ log 3 ≤ 1.098612288668111743876445 := by
  obtain ⟨h1, h2⟩ := log_bounds_of (3 / 4) 25 (by norm_num [abs_of_pos])
  have e : log (3 / 4 : ℝ) = log 3 - 2 * log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [e] at h1 h2
  norm_num [Finset.sum_range_succ, abs_of_pos] at h1 h2
  obtain ⟨a, b⟩ := log2_b
  constructor <;> linarith

theorem log5_b : (1.609437912434098271883260 : ℝ) ≤ log 5 ∧ log 5 ≤ 1.609437912434102422715887 := by
  obtain ⟨h1, h2⟩ := log_bounds_of (5 / 4) 25 (by norm_num [abs_of_neg])
  have e : log (5 / 4 : ℝ) = log 5 - 2 * log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [e] at h1 h2
  norm_num [Finset.sum_range_succ, abs_of_neg] at h1 h2
  obtain ⟨a, b⟩ := log2_b
  constructor <;> linarith

/-- `log (8x/25) = log x + 3 log 2 - 2 log 5`. -/
theorem log_mul_8_25 (x : ℝ) (hx : 0 < x) : log (x * 8 / 25) = log x + 3 * log 2 - 2 * log 5 := by
  rw [Real.log_div (by positivity) (by norm_num), Real.log_mul hx.ne' (by norm_num),
    show (8 : ℝ) = 2 ^ 3 by norm_num, show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow, Real.log_pow]
  push_cast; ring

theorem logpi_b : (1.144729885849393351445595 : ℝ) ≤ log π ∧ log π ≤ 1.144729885849406990191297 := by
  have hp1 := Real.pi_gt_d20
  have hp2 := Real.pi_lt_d20
  obtain ⟨h1, -⟩ := log_bounds_of ((3.14159265358979323846 : ℝ) * 8 / 25) 8 (by norm_num [abs_of_neg])
  obtain ⟨-, h2⟩ := log_bounds_of ((3.14159265358979323847 : ℝ) * 8 / 25) 8 (by norm_num [abs_of_pos])
  have m1 : log ((3.14159265358979323846 : ℝ) * 8 / 25) ≤ log (π * 8 / 25) :=
    Real.log_le_log (by norm_num) (by linarith)
  have m2 : log (π * 8 / 25) ≤ log ((3.14159265358979323847 : ℝ) * 8 / 25) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [log_mul_8_25 π Real.pi_pos] at m1 m2
  norm_num [Finset.sum_range_succ, abs_of_neg, abs_of_pos] at h1 h2
  obtain ⟨a, b⟩ := log2_b
  obtain ⟨c, d⟩ := log5_b
  constructor <;> linarith

theorem logT0_eq : log (3000000000000 : ℝ) = log 3 + 12 * log 2 + 12 * log 5 := by
  rw [show (3000000000000 : ℝ) = 3 * 2 ^ 12 * 5 ^ 12 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  push_cast; ring


theorem logL0_eq : log ((3000000000000 : ℝ) / (2 * π)) = log 3 + 11 * log 2 + 12 * log 5 - log π := by
  rw [Real.log_div (by norm_num) (by positivity), Real.log_mul (by norm_num) Real.pi_pos.ne', logT0_eq]
  ring


theorem logT0_b : (28.729 : ℝ) ≤ log 3000000000000 ∧ log 3000000000000 ≤ 28.73 := by
  rw [logT0_eq]; obtain ⟨a, b⟩ := log2_b; obtain ⟨c, d⟩ := log3_b; obtain ⟨e, f⟩ := log5_b
  constructor <;> linarith

theorem loglogT0_b : (3.357929112888776801896520 : ℝ) ≤ log (log 3000000000000) ∧ log (log 3000000000000) ≤ 3.357929112888798990847425 := by
  obtain ⟨a, b⟩ := log2_b; obtain ⟨c, d⟩ := log3_b; obtain ⟨e, f⟩ := log5_b
  have hx := logT0_eq
  set x := log (3000000000000 : ℝ) with hxdef
  have hxpos : 0 < x := by linarith
  have id : log (x * 5 / 144) = log x + log 5 - (4 * log 2 + 2 * log 3) := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_mul hxpos.ne' (by norm_num),
      show (144 : ℝ) = 2 ^ 4 * 3 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]
    push_cast; ring
  obtain ⟨h1, -⟩ := log_bounds_of (0.997556715437382628243077 : ℝ) 8 (by norm_num [abs_of_pos])
  obtain ⟨-, h2⟩ := log_bounds_of (0.997556715437385242864822 : ℝ) 8 (by norm_num [abs_of_pos])
  have m1 : log (0.997556715437382628243077 : ℝ) ≤ log (x * 5 / 144) := Real.log_le_log (by norm_num) (by linarith)
  have m2 : log (x * 5 / 144) ≤ log (0.997556715437385242864822 : ℝ) := Real.log_le_log (by positivity) (by linarith)
  rw [id] at m1 m2
  norm_num [Finset.sum_range_succ, abs_of_neg, abs_of_pos] at h1 h2
  constructor <;> linarith

theorem inv2pi_b : (0.159154943091895335768511 : ℝ) ≤ 1 / (2 * π) ∧ 1 / (2 * π) ≤ 0.159154943091895335769018 := by
  have hp1 := Real.pi_gt_d20
  have hp2 := Real.pi_lt_d20
  constructor
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith


theorem J_b : J 3000000000000 ≤ (53493920955173805339826419034 / 10 ^ 66) := by
  obtain ⟨a, b⟩ := log2_b; obtain ⟨c, d⟩ := log3_b; obtain ⟨e, f⟩ := log5_b
  obtain ⟨g, h⟩ := logpi_b; obtain ⟨i, j⟩ := logT0_b; obtain ⟨k, l⟩ := loglogT0_b
  obtain ⟨w1, w2⟩ := inv2pi_b
  have hL0 := logL0_eq
  unfold J R
  set L0 := log ((3000000000000 : ℝ) / (2 * π))
  set A := L0 / 3 + 1 / 9
  have hA : A ≤ (1.098612288668111743876445 + 11 * 0.693147180559946181503315 + 12 * 1.609437912434102422715887 - 1.144729885849393351445595) / 3 + 1 / 9 := by simp only [A]; linarith
  have hA0 : 0 ≤ A := by simp only [A]; linarith
  have t2 : A / (2 * π * (3000000000000 : ℝ) ^ 3)
      ≤ ((1.098612288668111743876445 + 11 * 0.693147180559946181503315 + 12 * 1.609437912434102422715887 - 1.144729885849393351445595) / 3 + 1 / 9) * 0.159154943091895335769018 / (3000000000000 : ℝ) ^ 3 := by
    have : A / (2 * π * (3000000000000 : ℝ) ^ 3) = A * (1 / (2 * π)) / (3000000000000 : ℝ) ^ 3 := by
      field_simp
    rw [this]
    gcongr
  have t4 : (0.2573 : ℝ) / (4 * (3000000000000 : ℝ) ^ 4 * log 3000000000000)
      ≤ 0.2573 / (4 * (3000000000000 : ℝ) ^ 4 * 28.729) := by
    gcongr
  have : (2 * (0.1038 * log 3000000000000 + 0.2573 * log (log 3000000000000) + 9.3675) /
      (3000000000000 : ℝ) ^ 4) ≤ 2 * (0.1038 * 28.73 + 0.2573 * 3.357929112888798990847425 + 9.3675) / (3000000000000 : ℝ) ^ 4 := by
    gcongr
  -- numeric closure
  have hfin : 2 * (0.1038 * 28.73 + 0.2573 * 3.357929112888798990847425 + 9.3675) / (3000000000000 : ℝ) ^ 4
      + ((1.098612288668111743876445 + 11 * 0.693147180559946181503315 + 12 * 1.609437912434102422715887 - 1.144729885849393351445595) / 3 + 1 / 9) * 0.159154943091895335769018 / (3000000000000 : ℝ) ^ 3
      + 0.1038 / (4 * (3000000000000 : ℝ) ^ 4)
      + 0.2573 / (4 * (3000000000000 : ℝ) ^ 4 * 28.729) ≤ (53493920955173805339826419034 / 10 ^ 66) := by norm_num
  linarith

theorem cosh_le_two (x : ℝ) (hx : |x| ≤ 1) : Real.cosh x ≤ 2 := by
  have h1 : |x| ≤ |(1 : ℝ)| := by rw [abs_one]; exact hx
  refine le_trans (Real.cosh_le_cosh.mpr h1) ?_
  rw [Real.cosh_eq]
  have := Real.exp_one_lt_d9
  have := Real.exp_neg_one_lt_half
  linarith

/-- `log (2^a 3^b 5^c) = a log 2 + b log 3 + c log 5`. -/
theorem log_235 (a b c : ℕ) :
    log ((2 : ℝ) ^ a * 3 ^ b * 5 ^ c) = a * log 2 + b * log 3 + c * log 5 := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]

end LiThreshold.Cert
