import NormFormula.Analytic.Separability
import NormFormula.ContinuousLogic.LocalTypeNIP
import NormFormula.ContinuousLogic.NormAddLocalType
import NormFormula.ContinuousLogic.YFinitePatternNIP

/-!
# Local-type NIP for the bounded norm formula on `Y`

This file connects the complete-theory NIP theorem for the normalized norm
formula on each positive ball of `Y` to the concrete local parameter type
space.  The only analytic input needed by the unconditional BFT theorem is a
common Lipschitz constant for the realized parameter profiles.
-/

namespace NormFormula.HalfGraph.Y.ContinuousLanguage

noncomputable section

open NormFormula.ContinuousLogic
open TopologicalSpace

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.rowNonempty

/-- On a positive `Y`-ball, every realized parameter profile of the normalized
norm formula is `1 / (2R)`-Lipschitz in the row variable. -/
theorem normFormula_parameterProfilesLipschitzWith
    (R : ℝ) (hR : 0 < R) :
    MultiFormula.ParameterProfilesLipschitzWith
      (reductStructure R hR) normFormula
      ⟨1 / (2 * R), by positivity⟩ := by
  intro parameter
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [MultiFormula.parameterProfile_apply]
  change dist (normAddTruth R hR x parameter)
      (normAddTruth R hR y parameter) ≤
    (1 / (2 * R)) * dist x y
  rw [Subtype.dist_eq, Real.dist_eq]
  change |‖x.1 + parameter.1‖ / (2 * R) -
      ‖y.1 + parameter.1‖ / (2 * R)| ≤
    (1 / (2 * R)) * dist x y
  rw [← sub_div, abs_div, abs_of_pos (by positivity : 0 < 2 * R)]
  calc
    |‖x.1 + parameter.1‖ - ‖y.1 + parameter.1‖| / (2 * R) ≤
        ‖(x.1 + parameter.1) - (y.1 + parameter.1)‖ / (2 * R) :=
      div_le_div_of_nonneg_right
        (abs_norm_sub_norm_le _ _) (by positivity)
    _ = (1 / (2 * R)) * dist x y := by
      rw [add_sub_add_right_eq_sub,
        show dist x y = ‖x.1 - y.1‖ by
          change dist (x.1 : Y) y.1 = ‖x.1 - y.1‖
          rw [dist_eq_norm]]
      field_simp

/-- The complete-theory theorem already proved for `Y` descends to NIP on
the distinguished positive-ball structure. -/
theorem normFormula_isNIPOnStructure
    (R : ℝ) (hR : 0 < R) :
    MultiFormula.IsNIPOnStructure
      (reductStructure R hR) normFormula :=
  (normFormula_isNIPInCompleteTheory R hR).isNIPOnStructure

/-- On every positive `Y`-ball, every sequence of rows has a subsequence whose
norm-formula evaluations converge pointwise on the concrete local parameter
type space.  Galvin--Prikry and BFT are supplied internally by
`LocalTypeNIP`. -/
theorem normFormula_hasPointwiseConvergentSubsequenceOnLocalType
    (R : ℝ) (hR : 0 < R) :
    MultiFormula.HasPointwiseConvergentSubsequenceOnLocalType
      (reductStructure R hR) normFormula := by
  letI : SeparableSpace (reductStructure R hR).Row :=
    inferInstanceAs (SeparableSpace (PositiveNormBall Y R))
  exact MultiFormula.IsNIPInCompleteTheory.hasPointwiseConvergentSubsequenceOnLocalType
      (normFormula_isNIPInCompleteTheory R hR)
      (normFormula_parameterProfilesLipschitzWith R hR)

end

end NormFormula.HalfGraph.Y.ContinuousLanguage

namespace NormFormula.HalfGraph.Y

noncomputable section

open NormFormula.ContinuousLogic
open TopologicalSpace

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.rowNonempty

/-- In the common one-symbol norm-addition language, the normalized norm
formula is NIP on every positive `Y`-ball. -/
theorem normAddMultiFormula_isNIPOnStructure
    (R : ℝ) (hR : 0 < R) :
    MultiFormula.IsNIPOnStructure
      (normAddMultiStructure (E := Y) R hR) normAddMultiFormula := by
  apply MultiFormula.normAddMultiFormula_isNIPOnStructure_of_boundedLocalNIP
  simpa [normPredicateTranslate] using
    normPredicateTranslate_isBoundedLocalNIP

/-- Every sequence in a positive `Y`-ball has a subsequence whose normalized
norm profiles converge pointwise on the local parameter type space in the
same generic syntax used for `X` and the direct sum. -/
theorem normAddMultiFormula_hasPointwiseConvergentSubsequenceOnLocalType
    (R : ℝ) (hR : 0 < R) :
    MultiFormula.HasPointwiseConvergentSubsequenceOnLocalType
      (normAddMultiStructure (E := Y) R hR) normAddMultiFormula := by
  letI : SeparableSpace
      (normAddMultiStructure (E := Y) R hR).Row :=
    inferInstanceAs (SeparableSpace (PositiveNormBall Y R))
  exact
    MultiFormula.hasPointwiseConvergentSubsequenceOnLocalType_of_isNIPOnStructure
      (MultiFormula.normAddMultiFormula_parameterProfilesLipschitzWith R hR)
      (normAddMultiFormula_isNIPOnStructure R hR)

end

end NormFormula.HalfGraph.Y
