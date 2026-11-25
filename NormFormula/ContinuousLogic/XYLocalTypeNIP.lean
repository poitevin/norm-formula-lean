import NormFormula.ContinuousLogic.L2SumLocalNIP
import NormFormula.ContinuousLogic.XLocalTypeNIP
import NormFormula.ContinuousLogic.YLocalTypeNIP

/-!
# Local-type NIP for the bounded direct sum

The two factor pointwise-subsequence theorems are diagonalized.  Surjectivity
of the joint-factor Euclidean map identifies every direct-sum local type with
a jointly realizable pair of factor types, so coordinatewise convergence and
continuity of the Euclidean connective give convergence on the full sum type
space.
-/

namespace NormFormula.XY

noncomputable section

open Filter
open scoped Topology
open NormFormula.ContinuousLogic

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.rowNonempty


/-- Hence the normalized norm formula is NIP on every distinguished positive
ball of `X ⊕₂ Y`. -/
theorem normAddMultiFormula_isNIPOnStructure
    (R : ℝ) (hR : 0 < R) :
    MultiFormula.IsNIPOnStructure
      (normAddMultiStructure (E := XYSpace) R hR) normAddMultiFormula :=
  normAddMultiFormula_isNIPOnStructure_l2Sum R hR
    (X.normAddMultiFormula_isNIPOnStructure R hR)
    (HalfGraph.Y.normAddMultiFormula_isNIPOnStructure R hR)

end

end NormFormula.XY
