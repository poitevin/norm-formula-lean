import NormFormula.Analytic.L2SumStability
import NormFormula.Examples.XIPPattern
import NormFormula.ModelTheory.BoundedStability

/-!
# Stability of the norm formula on `X`

The general finite-dimensional-summand theorem uses coordinatewise
compactness and asymptotic Pythagoras to prove the double-limit criterion for the concrete interpretation
`normTranslate x y = ‖x + y‖` on the paper's distinguished space `XSpace`.
This file packages that result as stability on every pair of bounded
Banach-space sorts.
-/

namespace NormFormula.X

/-- The norm formula is stable on the distinguished space `X`, in the
bounded double-limit sense appropriate to continuous Banach logic. -/
theorem normTranslate_isStableOnBounded :
    NormFormula.IsStableOnBounded normTranslate :=
  NormFormula.l2Sum_norm_isStableOnBounded

end NormFormula.X
