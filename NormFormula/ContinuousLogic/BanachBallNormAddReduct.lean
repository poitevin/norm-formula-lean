import NormFormula.ContinuousLogic.BanachBallFormulaContinuity
import NormFormula.ContinuousLogic.FinitePatternTransfer
import NormFormula.ContinuousLogic.FullBanachBallTheoryIP
import NormFormula.ContinuousLogic.NormAdd

/-!
# Fixed-radius norm reducts of predicate-free Banach ball structures

At a fixed rational radius, the typed formula `d(x+y,0)` determines a
two-sorted one-predicate reduct.  This file translates the entire bounded
two-sorted syntax of that reduct into the predicate-free typed ball syntax.
Consequently, equality of complete ball theories implies equality of the
associated fixed-radius norm-reduct theories.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u v


/-- Transport only the output-radius index of a typed term. -/
def BallTerm.castRadius {n : ℕ} {context : BallContext n}
    {first second : ℚ≥0} (h : first = second)
    (term : BallTerm context first) : BallTerm context second :=
  h ▸ term

@[simp]
theorem BallTerm.realize_castRadius
    (S : RationalBallSystem.{u}) {n : ℕ} {context : BallContext n}
    {first second : ℚ≥0} (h : first = second)
    (term : BallTerm context first)
    (assignment : BallTerm.Assignment S context) :
    (term.castRadius h).realize S assignment =
      (h ▸ term.realize S assignment) := by
  subst second
  rfl

end

end NormFormula.ContinuousLogic
