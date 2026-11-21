import NormFormula.ContinuousLogic.BanachBallMixedNormAddReduct
import NormFormula.ModelTheory.YNormLocalNIP

/-!
# Norm-formula NIP for `Y` in the full Banach ball theory

The concrete bounded-local-NIP theorem for `‖x + y‖` on `Y` is first lifted
to complete-theory NIP for the norm reduct on independently bounded row and
parameter balls.  The mixed-radius syntax/reduct translation then reflects
any full-ball-theory IP witness into that reduct, giving the desired theorem
in the genuine predicate-free Banach language.
-/

namespace NormFormula.HalfGraph.Y

noncomputable section

open NormFormula.ContinuousLogic

/-- For every pair of rational row and parameter radii, the typed
norm-addition formula is NIP in the complete predicate-free Banach ball
theory of `Y`. -/
theorem predicateFreeNormAddFormula_isNIPInCompleteTheory_mixed
    (rowRadius parameterRadius : ℚ≥0) :
    (predicateFreeNormAddFormula rowRadius parameterRadius).IsNIPInCompleteTheory
      (standardBanachBallStructure Y) := by
  apply BallFormula.isNIPInCompleteTheory_of_mixedNormAddMulti
  apply
    normAddMultiFormula_isNIPInCompleteTheory_ballNormAddMixedMultiStructure_of_boundedLocalNIP
  simpa [normPredicateTranslate] using
    normPredicateTranslate_isBoundedLocalNIP

/-- The equal-radius form retained as a convenient compatibility wrapper. -/
theorem predicateFreeNormAddFormula_isNIPInCompleteTheory
    (radius : ℚ≥0) :
    (predicateFreeNormAddFormula radius radius).IsNIPInCompleteTheory
      (standardBanachBallStructure Y) :=
  predicateFreeNormAddFormula_isNIPInCompleteTheory_mixed radius radius

end

end NormFormula.HalfGraph.Y
