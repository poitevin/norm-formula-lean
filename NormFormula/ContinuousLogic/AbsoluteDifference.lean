import NormFormula.ContinuousLogic.Basic

/-!
# Absolute difference as a bounded connective

The absolute difference of two truth values is again a truth value.  This
connective lets a universally quantified sentence express exact equality of
two bounded formulae.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open scoped Topology

/-- Absolute difference of two bounded truth values. -/
def absoluteDifferenceTruth (values : Fin 2 → TruthValue) : TruthValue := by
  refine ⟨|(values 0 : ℝ) - (values 1 : ℝ)|, abs_nonneg _, ?_⟩
  rw [abs_le]
  constructor
  · linarith [(values 0).2.1, (values 1).2.2]
  · linarith [(values 0).2.2, (values 1).2.1]

@[simp]
theorem absoluteDifferenceTruth_coe (values : Fin 2 → TruthValue) :
    (absoluteDifferenceTruth values : ℝ) =
      |(values 0 : ℝ) - (values 1 : ℝ)| :=
  rfl

/-- Absolute difference as a binary continuous-logic connective. -/
def absoluteDifferenceConnective : Connective 2 where
  toFun := absoluteDifferenceTruth
  continuous_toFun := by
    have hzero : Continuous fun values : Fin 2 → TruthValue ↦
        (values 0 : ℝ) :=
      continuous_subtype_val.comp (continuous_apply 0)
    have hone : Continuous fun values : Fin 2 → TruthValue ↦
        (values 1 : ℝ) :=
      continuous_subtype_val.comp (continuous_apply 1)
    exact (hzero.sub hone).abs.subtype_mk _

/-- Absolute difference is zero exactly when its two inputs agree. -/
theorem absoluteDifferenceConnective_eq_zero_iff
    (values : Fin 2 → TruthValue) :
    absoluteDifferenceConnective values = zeroTruthValue ↔
      values 0 = values 1 := by
  constructor
  · intro h
    apply Subtype.ext
    have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) h
    change |(values 0 : ℝ) - (values 1 : ℝ)| = 0 at hcoe
    exact sub_eq_zero.mp (abs_eq_zero.mp hcoe)
  · intro h
    apply Subtype.ext
    change |(values 0 : ℝ) - (values 1 : ℝ)| = 0
    rw [h, sub_self, abs_zero]

end

end NormFormula.ContinuousLogic
