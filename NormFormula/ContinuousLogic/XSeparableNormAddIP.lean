import NormFormula.ContinuousLogic.NormAddSeparableIP
import NormFormula.Examples.XIPPattern

/-!
# A separable elementary norm-predicate IP model for X

The concrete `sqrt 2`-bounded cube patterns yield a public separable model of
the same normalized positive-ball norm-predicate theory, with the explicit
positive normalized `sqrt 3`/`sqrt 6` gap and an infinite witness.
-/

namespace NormFormula.X

noncomputable section

open NormFormula.ContinuousLogic
open Set TopologicalSpace

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.parameterPseudoMetricSpace MultiStructure.rowNonempty
  MultiStructure.parameterNonempty

/-- The positive-ball radius used to contain the fixed `sqrt 2` row and
parameter bounds of the cube patterns in `XSpace`. -/
def separableNormAddRadius : ℝ :=
  1 + |Real.sqrt 2| + |Real.sqrt 2|

theorem separableNormAddRadius_pos : 0 < separableNormAddRadius := by
  unfold separableNormAddRadius
  positivity

/-- The concrete cube patterns in `XSpace` yield a separable model of the
same normalized norm-predicate theory with an infinite fixed-gap witness. -/
theorem exists_separableNormAddIPModel :
    ∃ N : MultiStructure.{0, 0, 0} NormAddSymbol,
      MultiSameCompleteTheory
        (normAddMultiStructure (E := XSpace) separableNormAddRadius
          separableNormAddRadius_pos) N ∧
      IsSeparable (Set.univ : Set N.Row) ∧
      IsSeparable (Set.univ : Set N.Parameter) ∧
      Real.sqrt 3 / (2 * separableNormAddRadius) <
        Real.sqrt 6 / (2 * separableNormAddRadius) ∧
      MultiFormula.HasInfiniteIPWitness N normAddMultiFormula
        (Real.sqrt 3 / (2 * separableNormAddRadius))
        (Real.sqrt 6 / (2 * separableNormAddRadius)) := by
  obtain ⟨N, hTheory, hRowSeparable, hParameterSeparable, hWitness⟩ :=
    exists_separableNormAddIPModel_of_patterns
      (E := XSpace) (Real.sqrt 2) (Real.sqrt 2)
      (Real.sqrt 3) (Real.sqrt 6)
      normTranslate_hasIPPatternsInEveryDimension
  have hgap : Real.sqrt 3 / (2 * separableNormAddRadius) <
      Real.sqrt 6 / (2 * separableNormAddRadius) :=
    (div_lt_div_iff_of_pos_right
      (mul_pos (by norm_num) separableNormAddRadius_pos)).2
      sqrtThree_lt_sqrtSix
  exact ⟨N, hTheory, hRowSeparable, hParameterSeparable, hgap, hWitness⟩

end

end NormFormula.X
