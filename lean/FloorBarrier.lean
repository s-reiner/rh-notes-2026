/-
Floor-class barrier: the algebraic core of notes/floor-class-barrier.tex, Proposition 1.

Within Liu's exponent comparison system (arXiv:2610.12234, §34), the two direct
constraints L0, LK, the floor-class constraint F (lowest zero class, trivial count R = 1,
amplitude x = 1/2), and b ≥ 0 (i.e. h ≥ 1 - M/2 + ℓ) force B ≥ (13 + 18 δ0) / (3 (5 + 6 δ0)),
independently of every zero-witness count.  At δ0 = 1/50 this is 167/192.

This file proves the pure inequality.  The meaning of the constraints is in the note and in
Liu's paper; nothing here depends on analytic number theory.
-/
import Mathlib.Tactic

noncomputable section
namespace FloorBarrier

/-- The direct constraints of Liu (25.1) and the floor constraint, as predicates on reals. -/
def L0 (M ℓ : ℝ) : ℝ := 5/6 + M/12 - ℓ/6
def LK (M ℓ : ℝ) : ℝ := 1/3 + 7*M/12 + ℓ/3
/-- Floor-class constraint: (18.4) with a = (1+δ0)/2, R = 1, x = 1/2, d = h. -/
def Floor (δ0 M ℓ h : ℝ) : ℝ := 1 + δ0 - (1 + δ0) * M / 2 + δ0 * ℓ + h / 3

/-- General floor: the barrier as a function of the detector floor δ0 ≥ 0. -/
theorem barrier_general (δ0 M ℓ h B : ℝ) (hδ : 0 ≤ δ0)
    (h0 : L0 M ℓ ≤ B) (hK : LK M ℓ ≤ B) (hF : Floor δ0 M ℓ h ≤ B)
    (hb : 1 - M/2 + ℓ ≤ h) :
    (13 + 18 * δ0) / (3 * (5 + 6 * δ0)) ≤ B := by
  unfold L0 LK Floor at *
  have hpos : 0 < 3 * (5 + 6 * δ0) := by positivity
  rw [div_le_iff₀ hpos]
  -- weights w0 = 2(5+9δ0)/(3(5+6δ0)), wK = 2/(3(5+6δ0)), wF = 1/(5+6δ0); multiply out by 3(5+6δ0)
  nlinarith [mul_nonneg hδ (sub_nonneg.mpr hF), mul_nonneg hδ (sub_nonneg.mpr h0),
             mul_nonneg hδ (sub_nonneg.mpr hK), mul_nonneg hδ (sub_nonneg.mpr hb)]

/-- The case δ0 = 1/50 of the OpenAI/Liu detector floor a0 = 51/100: B ≥ 167/192. -/
theorem barrier_167_192 (M ℓ h B : ℝ)
    (h0 : L0 M ℓ ≤ B) (hK : LK M ℓ ≤ B) (hF : Floor (1/50) M ℓ h ≤ B)
    (hb : 1 - M/2 + ℓ ≤ h) :
    (167 : ℝ) / 192 ≤ B := by
  unfold L0 LK Floor at *
  linarith

/-- The equality case: at M = 13/16, ℓ = 3/16, h = 25/32 all three constraints equal 167/192. -/
example : L0 (13/16) (3/16) = 167/192 ∧ LK (13/16) (3/16) = 167/192 ∧
    Floor (1/50) (13/16) (3/16) (25/32) = 167/192 := by
  unfold L0 LK Floor; norm_num

/-- The limit δ0 → 0 of the barrier is 13/15. -/
example : (13 + 18 * (0:ℝ)) / (3 * (5 + 6 * 0)) = 13/15 := by norm_num

end FloorBarrier
end

#print axioms FloorBarrier.barrier_general
#print axioms FloorBarrier.barrier_167_192
