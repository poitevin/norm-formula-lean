import NormFormula.ContinuousLogic.NormAdd
import NormFormula.ModelTheory.XTheorem

/-!
# The continuous-syntax specialization for `X`

The abstract formula token in the earlier theorem about `X` is instantiated
here by the actual atomic formula of the minimal bounded continuous language.
Metric-ultrapower compactness makes the specialization unconditional.
-/

namespace NormFormula.X

noncomputable section

open NormFormula.ContinuousLogic

/-- The actual continuous-formula semantics for norm addition on `XSpace`. -/
def continuousNormIPSemantics :
    NormFormula.CompleteTheoryIPSemantics XSpace XSpace :=
  normCompleteTheoryIPSemantics XSpace

/-- The unit token of the specialized interface denotes the concrete norm
translation predicate. -/
def continuousNormIPPresentation
    : CompleteTheoryIPPresentation continuousNormIPSemantics where
  normFormula := ()
  normFormula_value := rfl

/-- The concrete cube patterns imply semantic IP in the complete continuous
theory of `X`. -/
theorem normFormula_hasIPInSemanticCompleteTheory :
    NormFormulaHasIPInCompleteTheory XSpace := by
  exact continuousNormIPPresentation.normFormula_isIPInCompleteTheory

/-- The theorem about `X` with genuine formula syntax and complete-theory
semantics. -/
theorem normFormula_stableInX_and_hasSemanticTheoryIP :
    NormFormula.IsStableOnBounded normTranslate ∧
      NormFormulaHasIPInCompleteTheory XSpace := by
  exact ⟨normTranslate_isStableOnBounded,
    normFormula_hasIPInSemanticCompleteTheory⟩

end


end NormFormula.X
