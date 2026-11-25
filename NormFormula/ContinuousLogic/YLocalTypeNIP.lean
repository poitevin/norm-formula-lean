import NormFormula.Analytic.Separability
import NormFormula.ContinuousLogic.LocalTypeNIP
import NormFormula.ContinuousLogic.NormAddLocalType
import NormFormula.ModelTheory.YNormLocalNIP

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


end

end NormFormula.HalfGraph.Y
