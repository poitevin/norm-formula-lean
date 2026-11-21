import NormFormula.ContinuousLogic.BanachBallTermRestriction

/-!
# Restriction of atomic ball-formula evaluation

Normalized distance atoms and named-predicate atoms have the same value in
the closed generated structure as in the ambient structure on the included
assignment.  Distance uses the inherited metric and sort bound; predicates
use their definition by restriction.  Both cases reduce to typed term
restriction.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u w

namespace BallWitnessIndexing

variable {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
  {M : BallStructure.{u, w} Symbol symbolRadius}

/-- Normalized distance atoms commute with restriction to the closed ball
carriers. -/
theorem distance_realize_limitBallStructure_eq_ambient [Encodable Symbol]
    (initial : BallWitnessIndexing M)
    {n : ℕ} {context : BallContext n} {radius : ℚ≥0}
    (left right : BallTerm context radius)
    (assignment : BallTerm.Assignment
      initial.limitRationalBallSystem context) :
    (BallFormula.distance left right).realize initial.limitBallStructure
        assignment =
      (BallFormula.distance left right).realize M
        (initial.includeLimitBallAssignment assignment) := by
  apply Subtype.ext
  rw [BallFormula.realize_distance, BallFormula.realize_distance]
  have hleft :=
    initial.term_realize_limitBallStructure_eq_ambient left assignment
  have hright :=
    initial.term_realize_limitBallStructure_eq_ambient right assignment
  change (left.realize initial.limitRationalBallSystem assignment).1 = _
    at hleft
  change (right.realize initial.limitRationalBallSystem assignment).1 = _
    at hright
  change
    dist (left.realize initial.limitRationalBallSystem assignment).1
        (right.realize initial.limitRationalBallSystem assignment).1 /
          M.sortBound radius =
      dist (left.realize M.toRationalBallSystem
          (initial.includeLimitBallAssignment assignment))
        (right.realize M.toRationalBallSystem
          (initial.includeLimitBallAssignment assignment)) /
          M.sortBound radius
  rw [hleft, hright]

/-- Named-predicate atoms commute with restriction to the closed ball
carriers. -/
theorem predicate_realize_limitBallStructure_eq_ambient [Encodable Symbol]
    (initial : BallWitnessIndexing M)
    {n : ℕ} {context : BallContext n} (symbol : Symbol)
    (term : BallTerm context (symbolRadius symbol))
    (assignment : BallTerm.Assignment
      initial.limitRationalBallSystem context) :
    (BallFormula.predicate symbol term).realize initial.limitBallStructure
        assignment =
      (BallFormula.predicate symbol term).realize M
        (initial.includeLimitBallAssignment assignment) := by
  rw [BallFormula.realize_predicate, BallFormula.realize_predicate]
  change
    M.predicate symbol
        (initial.limitBallInclusion _
          (term.realize initial.limitRationalBallSystem assignment)) =
      M.predicate symbol
        (term.realize M.toRationalBallSystem
          (initial.includeLimitBallAssignment assignment))
  rw [initial.term_realize_limitBallStructure_eq_ambient term assignment]

end BallWitnessIndexing

end

end NormFormula.ContinuousLogic
