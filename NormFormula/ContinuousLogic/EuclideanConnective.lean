import NormFormula.ContinuousLogic.Basic
import NormFormula.ModelTheory.ConnectiveClosure
import Mathlib.Topology.Constructions.SumProd

/-!
# The bounded Euclidean connective

The augmented norm is reconstructed from two nonnegative predicates by the
Euclidean connective.  Continuous logic requires truth values in `[0,1]`, so
this file clips the real-valued Euclidean connective at `1` and packages the
result as a binary `Connective`.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open scoped Topology

/-- The Euclidean combination of two truth values, clipped at `1`. -/
def boundedEuclideanTruth (values : Fin 2 → TruthValue) : TruthValue :=
  ⟨min 1 (NormFormula.euclideanConnective (values 0) (values 1)),
    le_min (by norm_num) (Real.sqrt_nonneg _), min_le_left _ _⟩


/-- The clipped Euclidean operation as a binary continuous-logic
connective. -/
def boundedEuclideanConnective : Connective 2 where
  toFun := boundedEuclideanTruth
  continuous_toFun := by
    have hzero : Continuous fun values : Fin 2 → TruthValue ↦
        (values 0 : ℝ) :=
      continuous_subtype_val.comp (continuous_apply 0)
    have hone : Continuous fun values : Fin 2 → TruthValue ↦
        (values 1 : ℝ) :=
      continuous_subtype_val.comp (continuous_apply 1)
    have heuc : Continuous fun values : Fin 2 → TruthValue ↦
        NormFormula.euclideanConnective (values 0) (values 1) :=
      NormFormula.euclideanConnective_uniformContinuous.continuous.comp
        (hzero.prodMk hone)
    exact (continuous_const.min heuc).subtype_mk _


end

end NormFormula.ContinuousLogic
