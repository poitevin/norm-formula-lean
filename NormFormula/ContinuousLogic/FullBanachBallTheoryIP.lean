import NormFormula.ContinuousLogic.BanachBallCompactness
import NormFormula.Examples.XYIPPattern

/-!
# Norm-addition IP in the full predicate-free Banach ball theory

This file places the paper's norm formula directly in the standard
many-sorted rational-ball language of Banach spaces.  Thus no comparison
between the earlier one-predicate ultrapower and a Banach-space ultrapower is
needed: the existing cube patterns and typed compactness theorem already give
IP in the full predicate-free complete theory.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

/-- The norm of the sum of variables from prescribed rational-radius sorts,
represented in the predicate-free Banach ball language as distance to zero.
Its output term belongs to the sort of radius `rowRadius + parameterRadius`.
-/
def predicateFreeNormAddFormula (rowRadius parameterRadius : ℚ≥0) :
    BallFormula EmptyBallPredicate emptyBallPredicateRadius
      (![rowRadius, parameterRadius] : BallContext 2) :=
  .distance (BallTerm.binaryAddTerm rowRadius parameterRadius)
    (.zero (rowRadius + parameterRadius))

/-- In a standard Banach ball structure, the predicate-free norm-addition
formula is exactly the ambient norm of the sum divided by the metric bound of
its output sort. -/
theorem predicateFreeNormAddFormula_value
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (rowRadius parameterRadius : ℚ≥0)
    (assignment : BallTerm.Assignment
      (standardRationalBallSystem (E := E))
      (![rowRadius, parameterRadius] : BallContext 2)) :
    ((predicateFreeNormAddFormula rowRadius parameterRadius).realize
      (standardBanachBallStructure E) assignment : ℝ) =
      ‖(assignment 0).1 + (assignment 1).1‖ /
        rationalBallMetricBound (rowRadius + parameterRadius) := by
  unfold predicateFreeNormAddFormula
  rw [standard_distance_formula_value,
    BallTerm.binaryAddTerm_standardValue, BallTerm.standardValue_zero,
    dist_zero_right]

/-- The radius-`2` specialization used by the paper's cube witnesses has
truth value `‖x+y‖/8`. -/
theorem predicateFreeNormAddFormula_two_value
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (assignment : BallTerm.Assignment
      (standardRationalBallSystem (E := E))
      (![(2 : ℚ≥0), (2 : ℚ≥0)] : BallContext 2)) :
    ((predicateFreeNormAddFormula 2 2).realize
      (standardBanachBallStructure E) assignment : ℝ) =
      ‖(assignment 0).1 + (assignment 1).1‖ / 8 := by
  rw [predicateFreeNormAddFormula_value]
  norm_num [rationalBallMetricBound]

/-- The normalized cube levels retain a strict gap. -/
theorem normalizedSqrtThree_lt_normalizedSqrtSix :
    Real.sqrt 3 / 8 < Real.sqrt 6 / 8 :=
  div_lt_div_of_pos_right NormFormula.X.sqrtThree_lt_sqrtSix (by norm_num)

end

end NormFormula.ContinuousLogic

namespace NormFormula.X

noncomputable section

open NormFormula.ContinuousLogic

/-- The concrete X cube patterns are finite IP patterns for the norm formula
in the full predicate-free Banach ball language. -/
theorem predicateFreeNormAddFormula_hasFiniteIPPatternsInEveryDimension :
    (predicateFreeNormAddFormula 2 2).HasFiniteIPPatternsInEveryDimension
      (standardBanachBallStructure XSpace)
      (Real.sqrt 3 / 8) (Real.sqrt 6 / 8) := by
  have hsqrtTwo_le_two : Real.sqrt 2 ≤ 2 := by
    have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hsqrtNonneg := Real.sqrt_nonneg 2
    nlinarith
  intro n
  let rows : Fin n → (standardBanachBallStructure XSpace).Ball 2 := fun i ↦
    ⟨rowInX i, by
      rw [norm_rowInX]
      exact hsqrtTwo_le_two⟩
  refine ⟨rows, ?_⟩
  intro subset
  obtain ⟨parameter, hhigh, hlow⟩ := normTranslate_IPPattern n subset
  let typedParameter : (standardBanachBallStructure XSpace).Ball 2 :=
    ⟨parameter.1, parameter.2.trans hsqrtTwo_le_two⟩
  refine ⟨typedParameter, ?_, ?_⟩
  · intro i hi
    have h := hhigh i hi
    change Real.sqrt 6 / 8 ≤
      (predicateFreeNormAddFormula 2 2).binaryValue
        (standardBanachBallStructure XSpace) (rows i) typedParameter
    rw [BallFormula.binaryValue, predicateFreeNormAddFormula_two_value]
    exact div_le_div_of_nonneg_right h (by norm_num)
  · intro i hi
    have h := hlow i hi
    change (predicateFreeNormAddFormula 2 2).binaryValue
        (standardBanachBallStructure XSpace) (rows i) typedParameter ≤
      Real.sqrt 3 / 8
    rw [BallFormula.binaryValue, predicateFreeNormAddFormula_two_value]
    exact div_le_div_of_nonneg_right h (by norm_num)

/-- The norm formula has IP in the complete theory of X in the full standard
predicate-free Banach ball language. -/
theorem predicateFreeNormAddFormula_hasIPInCompleteTheory :
    (predicateFreeNormAddFormula 2 2).HasIPInCompleteTheory
      (standardBanachBallStructure XSpace) :=
  BallFormula.finitePatternCompactness
    (standardBanachBallStructure XSpace)
    (predicateFreeNormAddFormula 2 2)
    (Real.sqrt 3 / 8) (Real.sqrt 6 / 8)
    normalizedSqrtThree_lt_normalizedSqrtSix
    predicateFreeNormAddFormula_hasFiniteIPPatternsInEveryDimension

end

end NormFormula.X

namespace NormFormula.XY

noncomputable section

open NormFormula.ContinuousLogic

/-- The embedded X cube patterns are finite IP patterns for the norm formula
on `X ⊕₂ Y` in the full predicate-free Banach ball language. -/
theorem predicateFreeNormAddFormula_hasFiniteIPPatternsInEveryDimension :
    (predicateFreeNormAddFormula 2 2).HasFiniteIPPatternsInEveryDimension
      (standardBanachBallStructure XYSpace)
      (Real.sqrt 3 / 8) (Real.sqrt 6 / 8) := by
  have hsqrtTwo_le_two : Real.sqrt 2 ≤ 2 := by
    have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hsqrtNonneg := Real.sqrt_nonneg 2
    nlinarith
  intro n
  let rows : Fin n → (standardBanachBallStructure XYSpace).Ball 2 := fun i ↦
    ⟨cubeRow i, by
      rw [norm_cubeRow]
      exact hsqrtTwo_le_two⟩
  refine ⟨rows, ?_⟩
  intro subset
  obtain ⟨parameter, hhigh, hlow⟩ := normTranslate_IPPattern n subset
  let typedParameter : (standardBanachBallStructure XYSpace).Ball 2 :=
    ⟨parameter.1, parameter.2.trans hsqrtTwo_le_two⟩
  refine ⟨typedParameter, ?_, ?_⟩
  · intro i hi
    have h := hhigh i hi
    change Real.sqrt 6 / 8 ≤
      (predicateFreeNormAddFormula 2 2).binaryValue
        (standardBanachBallStructure XYSpace) (rows i) typedParameter
    rw [BallFormula.binaryValue, predicateFreeNormAddFormula_two_value]
    exact div_le_div_of_nonneg_right h (by norm_num)
  · intro i hi
    have h := hlow i hi
    change (predicateFreeNormAddFormula 2 2).binaryValue
        (standardBanachBallStructure XYSpace) (rows i) typedParameter ≤
      Real.sqrt 3 / 8
    rw [BallFormula.binaryValue, predicateFreeNormAddFormula_two_value]
    exact div_le_div_of_nonneg_right h (by norm_num)

/-- The norm formula has IP in the complete theory of `X ⊕₂ Y` in the
full standard predicate-free Banach ball language. -/
theorem predicateFreeNormAddFormula_hasIPInCompleteTheory :
    (predicateFreeNormAddFormula 2 2).HasIPInCompleteTheory
      (standardBanachBallStructure XYSpace) :=
  BallFormula.finitePatternCompactness
    (standardBanachBallStructure XYSpace)
    (predicateFreeNormAddFormula 2 2)
    (Real.sqrt 3 / 8) (Real.sqrt 6 / 8)
    normalizedSqrtThree_lt_normalizedSqrtSix
    predicateFreeNormAddFormula_hasFiniteIPPatternsInEveryDimension

end

end NormFormula.XY
