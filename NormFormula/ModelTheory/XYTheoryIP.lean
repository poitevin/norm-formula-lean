import NormFormula.Examples.XYIPPattern
import NormFormula.ModelTheory.ContinuousIP

/-!
# Theory-level IP for the norm formula on `X ⊕₂ Y`

This file packages the compactness conclusion from the direct-sum corollary.
All finite-pattern data come from the embedded first summand; only the same
explicit continuous-compactness interface used for `Th(X)` remains as a
semantic parameter.
-/

namespace NormFormula.XY

universe w

/-- Identification of the reduct-language norm formula with norm translation
on the distinguished direct sum. -/
structure CompleteTheoryIPPresentation
    (S : NormFormula.CompleteTheoryIPSemantics XYSpace XYSpace) where
  normFormula : S.Formula
  normFormula_value : S.formulaValue normFormula = normTranslate

namespace CompleteTheoryIPPresentation

variable {S : NormFormula.CompleteTheoryIPSemantics XYSpace XYSpace}

/-- The norm formula has IP in `Th(X ⊕₂ Y)`, conditional exactly on the
continuous-compactness field in `CompleteTheoryIPSemantics`. -/
theorem normFormula_isIPInCompleteTheory
    (P : CompleteTheoryIPPresentation S) :
    S.IsIPInTheory P.normFormula := by
  exact S.isIPInTheory_of_value_eq_of_finitePatterns
    P.normFormula normTranslate P.normFormula_value
    (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 6)
    X.sqrtThree_lt_sqrtSix normTranslate_hasIPPatternsInEveryDimension


end CompleteTheoryIPPresentation

end NormFormula.XY
