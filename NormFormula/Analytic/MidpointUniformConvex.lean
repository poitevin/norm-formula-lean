import Mathlib.Analysis.Convex.Uniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# A quantitative midpoint criterion for uniform convexity

The paper repeatedly uses the same fixed midpoint estimate.  This file records
once and for all that the estimate with constant `1 / 12` supplies Mathlib's
standard `UniformConvexSpace` structure.
-/

namespace NormFormula

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A norm satisfying the paper's quadratic midpoint estimate is uniformly
convex.  The proof extracts the explicit modulus
`min 1 (ε² / 12)`. -/
@[reducible] def uniformConvexSpaceOfMidpointEstimate
    (hmidpoint : ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤
        1 - (1 / 12 : ℝ) * ‖x - y‖ ^ 2) :
    UniformConvexSpace E where
  uniform_convex {ε} hε := by
    let δ : ℝ := min 1 (ε ^ 2 / 12)
    have hδ : 0 < δ := by
      exact lt_min one_pos (div_pos (sq_pos_of_pos hε) (by norm_num))
    refine ⟨δ, hδ, ?_⟩
    intro x hx y hy hxy
    by_cases hεtwo : ε ≤ 2
    · have hmid := hmidpoint x y hx.le hy.le
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hmid
      have hsum_nonneg : 0 ≤ ‖x + y‖ := norm_nonneg _
      have hsum_le_two : ‖x + y‖ ≤ 2 := by
        calc
          ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
          _ = 2 := by rw [hx, hy]; norm_num
      have hdist_nonneg : 0 ≤ ‖x - y‖ := norm_nonneg _
      have heps_sq_le : ε ^ 2 ≤ ‖x - y‖ ^ 2 :=
        (sq_le_sq₀ hε.le hdist_nonneg).2 hxy
      have heps_sq_le_four : ε ^ 2 ≤ 4 := by
        nlinarith [sq_nonneg (2 - ε)]
      have htarget_nonneg : 0 ≤ 2 - ε ^ 2 / 12 := by nlinarith
      have hsquares : ‖x + y‖ ^ 2 ≤ (2 - ε ^ 2 / 12) ^ 2 := by
        nlinarith [sq_nonneg (ε ^ 2)]
      have hstrong : ‖x + y‖ ≤ 2 - ε ^ 2 / 12 :=
        (sq_le_sq₀ hsum_nonneg htarget_nonneg).mp hsquares
      have hδle : δ ≤ ε ^ 2 / 12 := min_le_right _ _
      linarith
    · have hdist_le_two : ‖x - y‖ ≤ 2 := by
        calc
          ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
          _ = 2 := by rw [hx, hy]; norm_num
      exact (hεtwo (hxy.trans hdist_le_two)).elim

end

end NormFormula
