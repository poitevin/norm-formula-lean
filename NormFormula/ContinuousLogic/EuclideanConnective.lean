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

@[simp]
theorem boundedEuclideanTruth_coe (values : Fin 2 → TruthValue) :
    (boundedEuclideanTruth values : ℝ) =
      min 1 (NormFormula.euclideanConnective (values 0) (values 1)) :=
  rfl

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

/-- If the ordinary Euclidean value is already at most `1`, clipping is
inactive. -/
theorem boundedEuclideanConnective_eq_of_le_one
    (values : Fin 2 → TruthValue)
    (hvalues : NormFormula.euclideanConnective (values 0) (values 1) ≤ 1) :
    ((boundedEuclideanConnective values : TruthValue) : ℝ) =
      NormFormula.euclideanConnective (values 0) (values 1) := by
  exact min_eq_right hvalues

end

end NormFormula.ContinuousLogic
