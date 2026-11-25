import NormFormula.ContinuousLogic.BanachBallLimitStructure

/-!
# Restriction of typed term evaluation to the closed ball carriers

Including a finite assignment from the closed generated carriers into the
ambient ball structure commutes with evaluation of every typed Banach term.
The proof is by structural induction and uses the defining compatibility of
the restricted operations with carrier inclusion.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u w

namespace BallWitnessIndexing

variable {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
  {M : BallStructure.{u, w} Symbol symbolRadius}

/-- Include a finite dependent assignment from the closed limit structure
into the ambient ball structure. -/
def includeLimitBallAssignment [Encodable Symbol]
    (initial : BallWitnessIndexing M)
    {n : ℕ} {context : BallContext n} :
    BallTerm.Assignment initial.limitRationalBallSystem context →
      BallTerm.Assignment M.toRationalBallSystem context :=
  fun assignment i ↦ initial.limitBallInclusion (context i) (assignment i)


/-- Evaluation of every typed term commutes with inclusion of the closed
generated carriers into the ambient ball structure. -/
theorem term_realize_limitBallStructure_eq_ambient [Encodable Symbol]
    (initial : BallWitnessIndexing M)
    {n : ℕ} {context : BallContext n} {radius : ℚ≥0}
    (term : BallTerm context radius)
    (assignment : BallTerm.Assignment
      initial.limitRationalBallSystem context) :
    initial.limitBallInclusion radius
        (term.realize initial.limitRationalBallSystem assignment) =
      term.realize M.toRationalBallSystem
        (initial.includeLimitBallAssignment assignment) := by
  induction term with
  | «variable» i => rfl
  | inclusion h term induction =>
      change
        (term.realize initial.limitRationalBallSystem assignment).1 = _
        at induction
      rw [BallTerm.realize_inclusion, BallTerm.realize_inclusion]
      change
        (initial.carrierInclusion h
            (term.realize initial.limitRationalBallSystem assignment)).1 = _
      rw [carrierInclusion_val, induction]
  | zero radius =>
      rw [BallTerm.realize_zero, BallTerm.realize_zero]
      change (initial.carrierZero radius : M.Ball radius) = M.zero radius
      exact initial.carrierZero_val radius
  | neg term induction =>
      change
        (term.realize initial.limitRationalBallSystem assignment).1 = _
        at induction
      rw [BallTerm.realize_neg, BallTerm.realize_neg]
      change
        (initial.carrierNeg _
            (term.realize initial.limitRationalBallSystem assignment)).1 = _
      rw [carrierNeg_val, induction]
  | add left right leftInduction rightInduction =>
      change
        (left.realize initial.limitRationalBallSystem assignment).1 = _
        at leftInduction
      change
        (right.realize initial.limitRationalBallSystem assignment).1 = _
        at rightInduction
      rw [BallTerm.realize_add, BallTerm.realize_add]
      change
        (initial.carrierAdd _ _
            (left.realize initial.limitRationalBallSystem assignment,
              right.realize initial.limitRationalBallSystem assignment)).1 = _
      rw [carrierAdd_val, leftInduction, rightInduction]
  | smul q term induction =>
      change
        (term.realize initial.limitRationalBallSystem assignment).1 = _
        at induction
      rw [BallTerm.realize_smul, BallTerm.realize_smul]
      change
        (initial.carrierSmul q _
            (term.realize initial.limitRationalBallSystem assignment)).1 = _
      rw [carrierSmul_val, induction]

end BallWitnessIndexing

end

end NormFormula.ContinuousLogic
