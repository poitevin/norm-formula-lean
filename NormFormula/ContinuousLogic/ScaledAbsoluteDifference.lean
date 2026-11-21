import NormFormula.ContinuousLogic.Basic

/-!
# Scaled absolute difference as a bounded connective

For a scalar `c ∈ [0,1]`, the value `|x - c y|` is again in `[0,1]` and
vanishes exactly when `x = c y`.  This records equality between predicates
whose language normalizations use different fixed scales.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open scoped Topology

/-- The bounded truth value `|x - c y|` for `0 ≤ c ≤ 1`. -/
def scaledAbsoluteDifferenceTruth (c : ℝ) (hc : 0 ≤ c) (hcle : c ≤ 1)
    (values : Fin 2 → TruthValue) : TruthValue := by
  refine ⟨|(values 0 : ℝ) - c * (values 1 : ℝ)|, abs_nonneg _, ?_⟩
  have hscaled_nonneg : 0 ≤ c * (values 1 : ℝ) :=
    mul_nonneg hc (values 1).2.1
  have hscaled_le : c * (values 1 : ℝ) ≤ 1 := by
    calc
      c * (values 1 : ℝ) ≤ c * 1 :=
        mul_le_mul_of_nonneg_left (values 1).2.2 hc
      _ ≤ 1 := by simpa using hcle
  rw [abs_le]
  constructor <;> linarith [(values 0).2.1, (values 0).2.2]

@[simp]
theorem scaledAbsoluteDifferenceTruth_coe
    (c : ℝ) (hc : 0 ≤ c) (hcle : c ≤ 1)
    (values : Fin 2 → TruthValue) :
    (scaledAbsoluteDifferenceTruth c hc hcle values : ℝ) =
      |(values 0 : ℝ) - c * (values 1 : ℝ)| :=
  rfl

/-- Scaled absolute difference as a binary continuous connective. -/
def scaledAbsoluteDifferenceConnective
    (c : ℝ) (hc : 0 ≤ c) (hcle : c ≤ 1) : Connective 2 where
  toFun := scaledAbsoluteDifferenceTruth c hc hcle
  continuous_toFun := by
    have hleft : Continuous fun values : Fin 2 → TruthValue ↦
        (values 0 : ℝ) :=
      continuous_subtype_val.comp (continuous_apply 0)
    have hright : Continuous fun values : Fin 2 → TruthValue ↦
        (values 1 : ℝ) :=
      continuous_subtype_val.comp (continuous_apply 1)
    exact (hleft.sub (continuous_const.mul hright)).abs.subtype_mk _

/-- The scaled discrepancy vanishes exactly at the intended equality. -/
theorem scaledAbsoluteDifferenceConnective_eq_zero_iff
    (c : ℝ) (hc : 0 ≤ c) (hcle : c ≤ 1)
    (values : Fin 2 → TruthValue) :
    scaledAbsoluteDifferenceConnective c hc hcle values = zeroTruthValue ↔
      (values 0 : ℝ) = c * (values 1 : ℝ) := by
  constructor
  · intro h
    have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) h
    change |(values 0 : ℝ) - c * (values 1 : ℝ)| = 0 at hcoe
    exact sub_eq_zero.mp (abs_eq_zero.mp hcoe)
  · intro h
    apply Subtype.ext
    change |(values 0 : ℝ) - c * (values 1 : ℝ)| = 0
    rw [h, sub_self, abs_zero]

end

end NormFormula.ContinuousLogic
