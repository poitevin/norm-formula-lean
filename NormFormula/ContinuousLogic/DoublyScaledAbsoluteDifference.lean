import NormFormula.ContinuousLogic.Basic

/-!
# Doubly scaled absolute difference

For two coefficients in `[0,1]`, the value `|a*x - b*y|` is again a truth
value.  This connective expresses exact equality after independently undoing
two language normalizations.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open scoped Topology

/-- The bounded truth value `|a*x - b*y|` for `a,b ∈ [0,1]`. -/
def doublyScaledAbsoluteDifferenceTruth
    (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (values : Fin 2 → TruthValue) : TruthValue := by
  refine ⟨|a * (values 0 : ℝ) - b * (values 1 : ℝ)|, abs_nonneg _, ?_⟩
  have hleft0 : 0 ≤ a * (values 0 : ℝ) :=
    mul_nonneg ha0 (values 0).2.1
  have hleft1 : a * (values 0 : ℝ) ≤ 1 := by
    calc
      a * (values 0 : ℝ) ≤ a * 1 :=
        mul_le_mul_of_nonneg_left (values 0).2.2 ha0
      _ ≤ 1 := by simpa using ha1
  have hright0 : 0 ≤ b * (values 1 : ℝ) :=
    mul_nonneg hb0 (values 1).2.1
  have hright1 : b * (values 1 : ℝ) ≤ 1 := by
    calc
      b * (values 1 : ℝ) ≤ b * 1 :=
        mul_le_mul_of_nonneg_left (values 1).2.2 hb0
      _ ≤ 1 := by simpa using hb1
  rw [abs_le]
  constructor <;> linarith

@[simp] theorem doublyScaledAbsoluteDifferenceTruth_coe
    (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (values : Fin 2 → TruthValue) :
    (doublyScaledAbsoluteDifferenceTruth
        a b ha0 ha1 hb0 hb1 values : ℝ) =
      |a * (values 0 : ℝ) - b * (values 1 : ℝ)| :=
  rfl

/-- Doubly scaled absolute difference as a continuous connective. -/
def doublyScaledAbsoluteDifferenceConnective
    (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : Connective 2 where
  toFun := doublyScaledAbsoluteDifferenceTruth a b ha0 ha1 hb0 hb1
  continuous_toFun := by
    have hleft : Continuous fun values : Fin 2 → TruthValue ↦
        (values 0 : ℝ) :=
      continuous_subtype_val.comp (continuous_apply 0)
    have hright : Continuous fun values : Fin 2 → TruthValue ↦
        (values 1 : ℝ) :=
      continuous_subtype_val.comp (continuous_apply 1)
    exact ((continuous_const.mul hleft).sub
      (continuous_const.mul hright)).abs.subtype_mk _

/-- The connective vanishes exactly when the two scaled inputs agree. -/
theorem doublyScaledAbsoluteDifferenceConnective_eq_zero_iff
    (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (values : Fin 2 → TruthValue) :
    doublyScaledAbsoluteDifferenceConnective
        a b ha0 ha1 hb0 hb1 values = zeroTruthValue ↔
      a * (values 0 : ℝ) = b * (values 1 : ℝ) := by
  constructor
  · intro h
    have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) h
    change |a * (values 0 : ℝ) - b * (values 1 : ℝ)| = 0 at hcoe
    exact sub_eq_zero.mp (abs_eq_zero.mp hcoe)
  · intro h
    apply Subtype.ext
    change |a * (values 0 : ℝ) - b * (values 1 : ℝ)| = 0
    rw [h, sub_self, abs_zero]

end

end NormFormula.ContinuousLogic
