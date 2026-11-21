import NormFormula.ContinuousLogic.BanachBallAtomicRestriction

/-!
# Restriction through constants and connectives

Truth constants are structure-independent.  Every continuous connective,
and hence every rational clipped-affine/min/max connective used by the
countable ball-formula fragment, preserves equality of the values of its
children.  These are the non-quantified induction steps for rational
Tarski--Vaught.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u w

namespace BallWitnessIndexing

variable {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
  {M : BallStructure.{u, w} Symbol symbolRadius}

/-- Truth constants have the same value in the closed and ambient
structures. -/
theorem constant_realize_limitBallStructure_eq_ambient [Encodable Symbol]
    (initial : BallWitnessIndexing M)
    {n : ℕ} {context : BallContext n} (value : TruthValue)
    (assignment : BallTerm.Assignment
      initial.limitRationalBallSystem context) :
    (BallFormula.constant value : BallFormula Symbol symbolRadius context).realize
        initial.limitBallStructure assignment =
      (BallFormula.constant value : BallFormula Symbol symbolRadius context).realize
        M (initial.includeLimitBallAssignment assignment) :=
  rfl

/-- Any continuous connective preserves restriction equality once all of its
children do. -/
theorem connective_realize_limitBallStructure_eq_ambient [Encodable Symbol]
    (initial : BallWitnessIndexing M)
    {n arity : ℕ} {context : BallContext n}
    (connective : Connective arity)
    (formulas : Fin arity → BallFormula Symbol symbolRadius context)
    (assignment : BallTerm.Assignment
      initial.limitRationalBallSystem context)
    (hformulas : ∀ i,
      (formulas i).realize initial.limitBallStructure assignment =
        (formulas i).realize M
          (initial.includeLimitBallAssignment assignment)) :
    (BallFormula.connective connective formulas).realize
        initial.limitBallStructure assignment =
      (BallFormula.connective connective formulas).realize M
        (initial.includeLimitBallAssignment assignment) := by
  rw [BallFormula.realize_connective, BallFormula.realize_connective]
  congr 1
  funext i
  exact hformulas i

end BallWitnessIndexing

end

end NormFormula.ContinuousLogic
