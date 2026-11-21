import NormFormula.Examples.XIPPattern
import NormFormula.ModelTheory.SeparableIPModel

/-!
# A separable model of `Th(X)` with IP

All finite satisfiability data are supplied by the concrete cube patterns in
`XSpace`. The only remaining parameter is the explicit compactness and
downward-Löwenheim--Skolem interface from `SeparableIPModel`.
-/

namespace NormFormula.X

universe v w

variable (W : Type v)
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- Identification of the norm formula on the home space `X` and on the
separable extracted model `W`. -/
structure SeparableIPModelPresentation
    (S : NormFormula.SeparableIPModelSemantics XSpace W) where
  normFormula : S.Formula
  normFormula_homeValue : S.homeValue normFormula = normTranslate
  normFormula_modelValue :
    S.modelValue normFormula = fun x y : W ↦ ‖x + y‖
  finitePatternsToSeparableModel :
    S.ExtractsSeparableIPModel normFormula
      (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 6)

namespace SeparableIPModelPresentation

variable {W : Type v}
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
variable {S : NormFormula.SeparableIPModelSemantics XSpace W}

/-- Continuous compactness and downward Löwenheim--Skolem, fed the verified
cube patterns, produce a separable model of `Th(X)` whose actual norm formula
has one bounded infinite IP witness. -/
theorem extractedModel_isSeparable_and_norm_hasIP
    (P : SeparableIPModelPresentation W S) :
    S.IsModelOfHomeTheory ∧
      TopologicalSpace.IsSeparable (Set.univ : Set W) ∧
      NormFormula.HasBoundedInfiniteIPWitness
        (fun x y : W ↦ ‖x + y‖)
        (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 6) := by
  exact S.extract_of_value_eq_of_finitePatterns
    P.normFormula normTranslate (fun x y : W ↦ ‖x + y‖)
    P.normFormula_homeValue P.normFormula_modelValue
    (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 6)
    P.finitePatternsToSeparableModel
    sqrtThree_lt_sqrtSix normTranslate_hasIPPatternsInEveryDimension

end SeparableIPModelPresentation

end NormFormula.X
