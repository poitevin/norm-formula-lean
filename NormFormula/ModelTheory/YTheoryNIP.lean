import NormFormula.ModelTheory.ContinuousNIP
import NormFormula.ModelTheory.YNormLocalNIP

/-!
# The complete-theory NIP reduction for `Y`

This file packages the last paragraph of the manuscript's proof that the norm
formula is NIP in `Th(Y)`.  All concrete premises are discharged by earlier
Lean theorems.  What remains parameterized is exactly the continuous-logic
semantics isolated in `ContinuousNIPSemantics`.
-/

namespace NormFormula.HalfGraph.Y

universe w z

/-- A presentation of the three formulae used in the expanded-theory proof.
The value equations identify their interpretations in the distinguished
structure.  The final field is the theory-level reconstruction identity, not
merely its already-proved pointwise instance in `Y`. -/
structure CompleteTheoryPresentation
    (S : NormFormula.ContinuousNIPSemantics Y Y) where
  hilbertFormula : S.ExpansionFormula
  qFormula : S.ExpansionFormula
  normFormula : S.ReductFormula
  hilbertFormula_value :
    S.expansionValue hilbertFormula = hilbertNormPredicateTranslate
  qFormula_value : S.expansionValue qFormula = qPredicateTranslate
  normFormula_value : S.reductValue normFormula = normPredicateTranslate
  normFormula_equivalent :
    S.ExpansionEquivalent (S.liftReduct normFormula)
      (S.connective₂ NormFormula.euclideanConnective
        hilbertFormula qFormula)

namespace CompleteTheoryPresentation

variable {S : NormFormula.ContinuousNIPSemantics Y Y}

/-- The abstract continuous-logic principles, together with the fully proved
finite-pattern estimates, imply NIP of the norm formula in the complete theory
of the Banach reduct of `Y`. -/
theorem normFormula_isNIPInCompleteTheory
    (P : CompleteTheoryPresentation S) :
    S.IsNIPInReduct P.normFormula := by
  have hhBounded : NormFormula.IsBoundedOnNormBalls
      (S.expansionValue P.hilbertFormula) := by
    rw [P.hilbertFormula_value]
    exact hilbertNormPredicateTranslate_boundedOnNormBalls
  have hqBounded : NormFormula.IsBoundedOnNormBalls
      (S.expansionValue P.qFormula) := by
    rw [P.qFormula_value]
    exact qPredicateTranslate_boundedOnNormBalls
  have hhLocal : NormFormula.IsBoundedLocalNIP
      (S.expansionValue P.hilbertFormula) := by
    rw [P.hilbertFormula_value]
    exact hilbertNormPredicateTranslate_isBoundedLocalNIP
  have hqLocal : NormFormula.IsBoundedLocalNIP
      (S.expansionValue P.qFormula) := by
    rw [P.qFormula_value]
    exact qPredicateTranslate_isBoundedLocalNIP
  exact S.reduct_isNIP_of_equivalent_connective_of_local
    NormFormula.euclideanConnective
    NormFormula.euclideanConnective_uniformContinuous
    P.hilbertFormula P.qFormula P.normFormula
    hhBounded hqBounded hhLocal hqLocal P.normFormula_equivalent

/-- The reduct formula appearing in the preceding theorem really interprets
as the ambient norm translation predicate `‖x + y‖` on the distinguished
space `Y`. -/
theorem normFormula_value_eq_normPredicateTranslate
    (P : CompleteTheoryPresentation S) :
    S.reductValue P.normFormula = normPredicateTranslate :=
  P.normFormula_value

end CompleteTheoryPresentation

end NormFormula.HalfGraph.Y
