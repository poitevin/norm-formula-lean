import NormFormula.Examples.XIPPattern
import NormFormula.ModelTheory.ContinuousIP

/-!
# Theory-level IP for the norm formula on `X`

This file packages the compactness conclusion in the proof of the paper's
theorem about `X`.  Every geometric and finite-pattern premise is a proved
Lean theorem; only the syntax and continuous-compactness semantics remain an
explicit parameter.
-/

namespace NormFormula.X

universe w

/-- Identification of the reduct-language norm formula with its concrete
interpretation on the distinguished space `X`. -/
structure CompleteTheoryIPPresentation
    (S : NormFormula.CompleteTheoryIPSemantics XSpace XSpace) where
  normFormula : S.Formula
  normFormula_value : S.formulaValue normFormula = normTranslate

namespace CompleteTheoryIPPresentation

variable {S : NormFormula.CompleteTheoryIPSemantics XSpace XSpace}

/-- The norm formula has IP in `Th(X)`, conditional exactly on the explicit
continuous-compactness field of `CompleteTheoryIPSemantics`. -/
theorem normFormula_isIPInCompleteTheory
    (P : CompleteTheoryIPPresentation S) :
    S.IsIPInTheory P.normFormula := by
  exact S.isIPInTheory_of_value_eq_of_finitePatterns
    P.normFormula normTranslate P.normFormula_value
    (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 6)
    sqrtThree_lt_sqrtSix normTranslate_hasIPPatternsInEveryDimension

end CompleteTheoryIPPresentation

end NormFormula.X
