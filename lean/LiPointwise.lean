/-
Pointwise lemmas of the Li-positivity threshold note (notes/li-positivity-threshold.tex):
Lemma 1 (on-line pairs), Lemma 2 (off-line quadruples) — the parts that do not involve sums over zeros.
-/
import Mathlib

open Real

namespace LiThreshold

/-- Jordan-type inequality: `1 - cos x ≥ 2 x² / π²` for `|x| ≤ π`. -/
theorem one_sub_cos_ge (x : ℝ) (hx : |x| ≤ π) : 2 * x ^ 2 / π ^ 2 ≤ 1 - Real.cos x := by
  -- 1 - cos x = 2 sin²(x/2); Jordan: (2/π) t ≤ sin t for 0 ≤ t ≤ π/2.
  have h1 : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    have h2 : Real.cos x = Real.cos (2 * (x / 2)) := by ring_nf
    rw [h2, Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  rw [h1]
  -- reduce to t = |x|/2 ∈ [0, π/2]
  have ht0 : 0 ≤ |x| / 2 := by positivity
  have ht1 : |x| / 2 ≤ π / 2 := by linarith
  have hj : 2 / π * (|x| / 2) ≤ Real.sin (|x| / 2) := Real.mul_le_sin ht0 ht1
  have hsq : Real.sin (x / 2) ^ 2 = Real.sin (|x| / 2) ^ 2 := by
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h]; simp [Real.sin_neg, neg_div]
  rw [hsq]
  have hpos : 0 < π := Real.pi_pos
  have hs0 : 0 ≤ Real.sin (|x| / 2) := Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith)
  have hl : 0 ≤ 2 / π * (|x| / 2) := by positivity
  have hmul := mul_le_mul hj hj hl hs0
  have hx2 : (|x|) ^ 2 = x ^ 2 := sq_abs x
  calc 2 * x ^ 2 / π ^ 2 = 2 * ((2 / π * (|x| / 2)) * (2 / π * (|x| / 2))) := by
        rw [← hx2]; field_simp
    _ ≤ 2 * (Real.sin (|x| / 2) * Real.sin (|x| / 2)) := by linarith
    _ = 2 * Real.sin (|x| / 2) ^ 2 := by ring

/-- The angle of an on-line zero: for `ρ = 1/2 + iγ`, `w = 1 - 1/ρ` has `arg w = 2 arctan (1/(2γ))`;
we only need the elementary bounds on `θ(γ) := 2 arctan (1/(2γ))`. -/
noncomputable def theta (γ : ℝ) : ℝ := 2 * Real.arctan (1 / (2 * γ))

theorem theta_le (γ : ℝ) (hγ : 0 < γ) : theta γ ≤ 1 / γ := by
  unfold theta
  have h : Real.arctan (1 / (2 * γ)) ≤ 1 / (2 * γ) := by
    have hx : 0 ≤ 1 / (2 * γ) := by positivity
    exact Real.arctan_le_self hx  -- placeholder name; fixed below if absent
  calc 2 * Real.arctan (1 / (2 * γ)) ≤ 2 * (1 / (2 * γ)) := by linarith
    _ = 1 / γ := by field_simp

/-- `arctan x ≥ x - x³/3` for `x ≥ 0`, via the derivative of `arctan x - x + x³/3`, which is `x⁴/(1+x²) ≥ 0`. -/
theorem arctan_ge_sub_cube (x : ℝ) (hx : 0 ≤ x) : x - x ^ 3 / 3 ≤ Real.arctan x := by
  let f : ℝ → ℝ := fun t => Real.arctan t - t + t ^ 3 / 3
  have hderiv : ∀ t, HasDerivAt f (t ^ 4 / (1 + t ^ 2)) t := by
    intro t
    have h1 := Real.hasDerivAt_arctan t
    have h2 : HasDerivAt (fun t : ℝ => t ^ 3 / 3) (t ^ 2) t := by
      have := (hasDerivAt_pow 3 t).div_const 3
      convert this using 1; push_cast; ring
    have h := (h1.sub (hasDerivAt_id t)).add h2
    convert h using 1
    · ext t; simp [f]
    · field_simp; ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
    · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
    · intro t _; rw [(hderiv t).deriv]; positivity
  have h0 : f 0 = 0 := by simp [f]
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  rw [h0] at this
  simp only [f] at this
  linarith

theorem theta_ge (γ : ℝ) (hγ : 0 < γ) : 1 / γ - 1 / (12 * γ ^ 3) ≤ theta γ := by
  unfold theta
  have hx : 0 ≤ 1 / (2 * γ) := by positivity
  have h := arctan_ge_sub_cube (1 / (2 * γ)) hx
  have e : 2 * (1 / (2 * γ) - (1 / (2 * γ)) ^ 3 / 3) = 1 / γ - 1 / (12 * γ ^ 3) := by
    field_simp; ring
  linarith [e]

/-! ### Lemma 2: off-line quadruples -/

/-- The quadruple sum over `w, conj w, 1/w, 1/conj w` of `1 - z^n` is real and equals
`4 - 2 Re(w^n) - 2 Re(w^{-n})`. -/
theorem quad_sum_eq (w : ℂ) (n : ℕ) :
    (1 - w ^ n) + (1 - (starRingEnd ℂ w) ^ n) + (1 - w⁻¹ ^ n) + (1 - (starRingEnd ℂ w)⁻¹ ^ n)
      = ((4 - 2 * (w ^ n).re - 2 * (w⁻¹ ^ n).re : ℝ) : ℂ) := by
  have h1 : (starRingEnd ℂ w) ^ n = starRingEnd ℂ (w ^ n) := by rw [map_pow]
  have h2 : (starRingEnd ℂ w)⁻¹ ^ n = starRingEnd ℂ (w⁻¹ ^ n) := by rw [map_pow, map_inv₀]
  rw [h1, h2]
  have ha := Complex.add_conj (w ^ n)
  have hb := Complex.add_conj (w⁻¹ ^ n)
  push_cast at ha hb ⊢
  linear_combination (-1 : ℂ) * ha + (-1 : ℂ) * hb

/-- In polar form, `Re(w^n) + Re(w^{-n}) = (r^n + r^{-n}) cos(n θ)` with `r = ‖w‖`, `θ = arg w`. -/
theorem re_pow_add_re_inv_pow (w : ℂ) (hw : w ≠ 0) (n : ℕ) :
    (w ^ n).re + (w⁻¹ ^ n).re
      = (‖w‖ ^ n + ‖w‖⁻¹ ^ n) * Real.cos (n * Complex.arg w) := by
  have hpolar : w = (‖w‖ : ℂ) * Complex.exp (Complex.arg w * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I w).symm
  have e1 : w ^ n = ((‖w‖ ^ n : ℝ) : ℂ) * Complex.exp (((n * Complex.arg w : ℝ)) * Complex.I) := by
    conv_lhs => rw [hpolar]
    rw [mul_pow, ← Complex.exp_nat_mul]; push_cast; ring_nf
  have e2 : w⁻¹ ^ n = ((‖w‖⁻¹ ^ n : ℝ) : ℂ) * Complex.exp (((-(n * Complex.arg w) : ℝ)) * Complex.I) := by
    conv_lhs => rw [hpolar]
    rw [mul_inv, ← Complex.exp_neg, mul_pow, ← Complex.exp_nat_mul]; push_cast; ring_nf
  rw [e1, e2, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  ring

/-- `r^n + r^{-n} = 2 cosh(n log r)` for `r > 0`. -/
theorem pow_add_inv_pow_eq_cosh (r : ℝ) (hr : 0 < r) (n : ℕ) :
    r ^ n + r⁻¹ ^ n = 2 * Real.cosh (n * Real.log r) := by
  have h1 : r ^ n = Real.exp (n * Real.log r) := by rw [Real.exp_nat_mul, Real.exp_log hr]
  have h2 : r⁻¹ ^ n = Real.exp (-(n * Real.log r)) := by
    rw [show -(n * Real.log r) = n * (-Real.log r) by ring, Real.exp_nat_mul, Real.exp_neg, Real.exp_log hr]
  rw [h1, h2, Real.cosh_eq]; ring

/-- Lemma 2, inequality form: the real quadruple sum is `≥ 4 - 4 cosh(n log ‖w‖)`. -/
theorem quad_sum_ge (w : ℂ) (hw : w ≠ 0) (n : ℕ) :
    4 - 4 * Real.cosh (n * Real.log ‖w‖)
      ≤ 4 - 2 * (w ^ n).re - 2 * (w⁻¹ ^ n).re := by
  have hr : (0:ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  rw [show 4 - 2 * (w ^ n).re - 2 * (w⁻¹ ^ n).re = 4 - 2 * ((w ^ n).re + (w⁻¹ ^ n).re) by ring,
    re_pow_add_re_inv_pow w hw n, pow_add_inv_pow_eq_cosh _ hr n]
  have hc : 0 < Real.cosh (n * Real.log ‖w‖) := Real.cosh_pos _
  have hcos : Real.cos (n * Complex.arg w) ≤ 1 := Real.cos_le_one _
  nlinarith

theorem four_sub_four_cosh (x : ℝ) : 4 - 4 * Real.cosh x = -8 * Real.sinh (x / 2) ^ 2 := by
  have h : Real.cosh x = Real.cosh (2 * (x / 2)) := by ring_nf
  rw [h, Real.cosh_two_mul]; nlinarith [Real.cosh_sq (x / 2)]

/-- The logarithm estimate: `|log(1+x) - x| ≤ 2 x²` for `|x| ≤ 1/2`. -/
theorem abs_log_one_add_sub_le (x : ℝ) (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - x| ≤ 2 * x ^ 2 := by
  have hx1 : |(-x)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx1 1
  norm_num at h
  -- h : |-x + log (1 + x)| ≤ x ^ 2 / (1 - |x|)   (up to normal form)
  have hpos : 0 < 1 - |x| := by linarith
  have hd : x ^ 2 / (1 - |x|) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ hpos]; nlinarith [sq_nonneg x, abs_nonneg x]
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have e : -x + Real.log (1 + x) = Real.log (1 + x) - x := by ring
  rw [e] at h
  exact le_trans h hd

/-! ### The δ-bound: `|log ‖1 - 1/ρ‖| ≤ (|1-2β| + 2γ⁻²)/(2γ²)` for `ρ = β + iγ`, `|γ| ≥ 2`. -/

/-- `‖1 - 1/ρ‖² = 1 + (1 - 2β)/‖ρ‖²`. -/
theorem normSq_one_sub_inv (ρ : ℂ) (hρ : ρ ≠ 0) :
    Complex.normSq (1 - ρ⁻¹) = 1 + (1 - 2 * ρ.re) / Complex.normSq ρ := by
  have hn : Complex.normSq ρ ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  have : 1 - ρ⁻¹ = (ρ - 1) / ρ := by field_simp
  rw [this, Complex.normSq_div, Complex.normSq_sub, Complex.normSq_one]
  field_simp
  simp [Complex.normSq_apply, Complex.mul_re, Complex.one_re, Complex.one_im]
  ring

/-- For `ρ = β + iγ` with `|γ| ≥ 2` and `0 < β < 1`, writing `x = (1-2β)/‖ρ‖²` one has `|x| ≤ 1/γ² ≤ 1/4`. -/
theorem delta_bound (ρ : ℂ) (hβ0 : 0 < ρ.re) (hβ1 : ρ.re < 1) (hγ : 2 ≤ |ρ.im|) :
    |Real.log ‖1 - ρ⁻¹‖| ≤ (|1 - 2 * ρ.re| + 2 / ρ.im ^ 2) / (2 * ρ.im ^ 2) := by
  have hρ : ρ ≠ 0 := by intro h; rw [h] at hγ; simp at hγ; linarith
  have hγ2 : 4 ≤ ρ.im ^ 2 := by nlinarith [sq_abs ρ.im, abs_nonneg ρ.im]
  have hN : ρ.im ^ 2 ≤ Complex.normSq ρ := by
    rw [Complex.normSq_apply]; nlinarith [sq_nonneg ρ.re]
  have hNpos : 0 < Complex.normSq ρ := by linarith
  set x := (1 - 2 * ρ.re) / Complex.normSq ρ with hx
  have hx_abs : |x| ≤ 1 / ρ.im ^ 2 := by
    rw [hx, abs_div, abs_of_pos hNpos, div_le_div_iff₀ hNpos (by positivity)]
    have : |1 - 2 * ρ.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    nlinarith
  have hx_half : |x| ≤ 1 / 2 := by
    calc |x| ≤ 1 / ρ.im ^ 2 := hx_abs
      _ ≤ 1 / 2 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  -- log ‖w‖ = (1/2) log (normSq w) = (1/2) log (1 + x)
  have hw_pos : 0 < Complex.normSq (1 - ρ⁻¹) := by
    rw [normSq_one_sub_inv ρ hρ]; have := abs_le.mp hx_half; linarith
  have hlog : Real.log ‖1 - ρ⁻¹‖ = (1 / 2) * Real.log (1 + x) := by
    have hsq : Complex.normSq (1 - ρ⁻¹) = ‖1 - ρ⁻¹‖ ^ 2 := Complex.normSq_eq_norm_sq _
    have : Real.log (Complex.normSq (1 - ρ⁻¹)) = 2 * Real.log ‖1 - ρ⁻¹‖ := by
      rw [hsq, Real.log_pow]; push_cast; ring
    rw [normSq_one_sub_inv ρ hρ] at this
    linarith
  rw [hlog, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
  have hest := abs_log_one_add_sub_le x hx_half
  have htri : |Real.log (1 + x)| ≤ |x| + 2 * x ^ 2 := by
    have h1 := abs_le.mp hest
    have h2 := le_abs_self x
    have h3 := neg_abs_le x
    rw [abs_le]; constructor <;> linarith
  have hx2 : x ^ 2 ≤ 1 / ρ.im ^ 2 * (1 / ρ.im ^ 2) := by
    have := mul_le_mul hx_abs hx_abs (abs_nonneg x) (by positivity)
    rw [← sq_abs]; nlinarith
  have hxa : |x| ≤ |1 - 2 * ρ.re| / ρ.im ^ 2 := by
    rw [hx, abs_div, abs_of_pos hNpos, div_le_div_iff₀ hNpos (by positivity)]
    nlinarith [abs_nonneg (1 - 2 * ρ.re)]
  have hfin : |x| + 2 * x ^ 2 ≤ (|1 - 2 * ρ.re| + 2 / ρ.im ^ 2) / ρ.im ^ 2 := by
    rw [add_div]
    have e : 2 / ρ.im ^ 2 / ρ.im ^ 2 = 2 * (1 / ρ.im ^ 2 * (1 / ρ.im ^ 2)) := by field_simp
    rw [e]; linarith
  calc (1 / 2) * |Real.log (1 + x)| ≤ (1 / 2) * (|x| + 2 * x ^ 2) := by linarith
    _ ≤ (1 / 2) * ((|1 - 2 * ρ.re| + 2 / ρ.im ^ 2) / ρ.im ^ 2) := by linarith
    _ = (|1 - 2 * ρ.re| + 2 / ρ.im ^ 2) / (2 * ρ.im ^ 2) := by field_simp

end LiThreshold
