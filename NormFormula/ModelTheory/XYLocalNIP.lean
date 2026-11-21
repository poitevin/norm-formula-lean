import NormFormula.Examples.XYInstability
import NormFormula.Examples.XIPPattern
import NormFormula.ModelTheory.SequentialLocalNIP
import NormFormula.ModelTheory.YNormLocalNIP

/-!
# Local NIP of the norm on `X ⊕₂ Y`

This file specializes the sequential ℓ₂-sum closure theorem to the three
spaces in the paper. A presentation records the norm-formula tokens, their
interpretations on the home structures, and the coordinate identity in the
local parameter spaces (equivalently, in a sufficiently saturated
multisorted extension).

The theorem then discharges the entire closure argument: NIP of the norm
formula on the distinguished spaces `X` and `Y` implies NIP of the norm
formula on the distinguished direct sum. This is intentionally a local
conclusion and is compatible with the already proved fixed finite patterns
that yield IP in the complete theory.
-/

namespace NormFormula.XY

open scoped ENNReal

/-- The semantic data connecting the three local norm formulae and their
parameter spaces in the multisorted expansion used by the paper. -/
structure LocalNIPSumPresentation
    (SX : NormFormula.SequentialLocalNIPSemantics X.XSpace)
    (SY : NormFormula.SequentialLocalNIPSemantics HalfGraph.Y)
    (SXY : NormFormula.SequentialLocalNIPSemantics XYSpace) where
  xNormFormula : SX.Formula
  yNormFormula : SY.Formula
  xyNormFormula : SXY.Formula
  xHomeParameter : X.XSpace → SX.Parameter
  yHomeParameter : HalfGraph.Y → SY.Parameter
  xyHomeParameter : XYSpace → SXY.Parameter
  xNormFormula_value : ∀ x y,
    SX.formulaValue xNormFormula x (xHomeParameter y) = X.normTranslate x y
  yNormFormula_value : ∀ x y,
    SY.formulaValue yNormFormula x (yHomeParameter y) =
      HalfGraph.Y.normPredicateTranslate x y
  xyNormFormula_value : ∀ x y,
    SXY.formulaValue xyNormFormula x (xyHomeParameter y) = normTranslate x y
  parameterToX : SXY.Parameter → SX.Parameter
  parameterToY : SXY.Parameter → SY.Parameter
  l2NormIdentity : ∀ z p,
    SXY.formulaValue xyNormFormula z p =
      NormFormula.euclideanConnective
        (SX.formulaValue xNormFormula z.fst (parameterToX p))
        (SY.formulaValue yNormFormula z.snd (parameterToY p))

namespace LocalNIPSumPresentation

variable
    {SX : NormFormula.SequentialLocalNIPSemantics X.XSpace}
    {SY : NormFormula.SequentialLocalNIPSemantics HalfGraph.Y}
    {SXY : NormFormula.SequentialLocalNIPSemantics XYSpace}

/-- NIP of the two factor norm formulae on their distinguished spaces implies
NIP of the norm formula on the distinguished space `X ⊕₂ Y`. -/
theorem normFormula_isNIPOnDistinguished
    (P : LocalNIPSumPresentation SX SY SXY)
    (hx : SX.IsNIPOnDistinguished P.xNormFormula)
    (hy : SY.IsNIPOnDistinguished P.yNormFormula) :
    SXY.IsNIPOnDistinguished P.xyNormFormula := by
  exact NormFormula.SequentialLocalNIPSemantics.l2Sum_isNIPOnDistinguished
    SX SY SXY P.xNormFormula P.yNormFormula P.xyNormFormula
    P.parameterToX P.parameterToY P.l2NormIdentity hx hy

/-- The sum-formula token in the closure theorem really restricts to the
concrete norm-translation predicate on `XYSpace`. -/
theorem xyNormFormula_value_eq_normTranslate
    (P : LocalNIPSumPresentation SX SY SXY) :
    ∀ x y, SXY.formulaValue P.xyNormFormula x (P.xyHomeParameter y) =
      normTranslate x y :=
  P.xyNormFormula_value

end LocalNIPSumPresentation

end NormFormula.XY
