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


end

end NormFormula.ContinuousLogic
