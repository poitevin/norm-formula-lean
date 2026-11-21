import NormFormula.ContinuousLogic.NormAdd
import NormFormula.ModelTheory.XYTheoryIP

/-!
# The continuous-syntax specialization for `X ⊕₂ Y`

The direct sum uses the same bounded norm-addition language as `X`. Its
verified cube patterns feed the now-proved metric-ultrapower compactness
theorem.
-/

namespace NormFormula.XY

noncomputable section

open NormFormula.ContinuousLogic

/-- The actual continuous-formula semantics for norm addition on `XYSpace`. -/
def continuousNormIPSemantics :
    NormFormula.CompleteTheoryIPSemantics XYSpace XYSpace :=
  normCompleteTheoryIPSemantics XYSpace

/-- The unit token of the specialized interface denotes the concrete norm
translation predicate on the direct sum. -/
def continuousNormIPPresentation
    : CompleteTheoryIPPresentation continuousNormIPSemantics where
  normFormula := ()
  normFormula_value := rfl

/-- The embedded cube patterns give semantic IP in the complete theory of
`X ⊕₂ Y`. -/
theorem normFormula_hasIPInSemanticCompleteTheory :
    NormFormulaHasIPInCompleteTheory XYSpace := by
  exact continuousNormIPPresentation.normFormula_isIPInCompleteTheory

end


end NormFormula.XY
