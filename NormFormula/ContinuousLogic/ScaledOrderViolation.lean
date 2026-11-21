import NormFormula.ContinuousLogic.Basic

/-!
# A scaled order-violation connective

For nonnegative `c`, the connective

`max 0 (x - c * y)`

vanishes exactly when `x ≤ c * y`.  This lets a universally quantified
continuous-logic sentence express a uniform comparison between two bounded
predicates.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open scoped Topology

/-- The bounded truth value measuring failure of `x ≤ c * y`. -/
def scaledOrderViolationTruth (c : ℝ) (hc : 0 ≤ c)
    (values : Fin 2 → TruthValue) : TruthValue := by
  refine ⟨max 0 ((values 0 : ℝ) - c * (values 1 : ℝ)), le_max_left _ _, ?_⟩
  apply max_le
  · norm_num
  · nlinarith [(values 0).2.2, (values 1).2.1]

@[simp]
theorem scaledOrderViolationTruth_coe (c : ℝ) (hc : 0 ≤ c)
    (values : Fin 2 → TruthValue) :
    (scaledOrderViolationTruth c hc values : ℝ) =
      max 0 ((values 0 : ℝ) - c * (values 1 : ℝ)) :=
  rfl

/-- The scaled order violation as a binary continuous connective. -/
def scaledOrderViolationConnective (c : ℝ) (hc : 0 ≤ c) : Connective 2 where
  toFun := scaledOrderViolationTruth c hc
  continuous_toFun := by
    have hzero : Continuous fun _ : Fin 2 → TruthValue ↦ (0 : ℝ) :=
      continuous_const
    have hleft : Continuous fun values : Fin 2 → TruthValue ↦
        (values 0 : ℝ) :=
      continuous_subtype_val.comp (continuous_apply 0)
    have hright : Continuous fun values : Fin 2 → TruthValue ↦
        (values 1 : ℝ) :=
      continuous_subtype_val.comp (continuous_apply 1)
    exact (hzero.max (hleft.sub (continuous_const.mul hright))).subtype_mk _

/-- The violation connective vanishes exactly when the intended scaled
comparison holds. -/
theorem scaledOrderViolationConnective_eq_zero_iff
    (c : ℝ) (hc : 0 ≤ c) (values : Fin 2 → TruthValue) :
    scaledOrderViolationConnective c hc values = zeroTruthValue ↔
      (values 0 : ℝ) ≤ c * (values 1 : ℝ) := by
  constructor
  · intro h
    have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) h
    change max 0 ((values 0 : ℝ) - c * (values 1 : ℝ)) = 0 at hcoe
    have hle : (values 0 : ℝ) - c * (values 1 : ℝ) ≤
        max 0 ((values 0 : ℝ) - c * (values 1 : ℝ)) :=
      le_max_right _ _
    linarith
  · intro h
    apply Subtype.ext
    change max 0 ((values 0 : ℝ) - c * (values 1 : ℝ)) = 0
    rw [max_eq_left]
    linarith

end

end NormFormula.ContinuousLogic
