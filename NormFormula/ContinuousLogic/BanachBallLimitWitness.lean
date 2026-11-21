import NormFormula.ContinuousLogic.BanachBallWitnessLimit

/-!
# Rational quantifier witnesses inside the ball-sorted stage limit

A finite dependent assignment from the limit indices is lifted to its common
stage.  The associated rational quantifier request is adjoined at the next
stage, so its selected point becomes another limit index in exactly the
quantified radius.  Its ambient value satisfies the requested supremum or
infimum inequality for the original limit assignment.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u w

namespace BallWitnessIndexing

variable {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
  {M : BallStructure.{u, w} Symbol symbolRadius}

/-- The common-stage request associated to a rational formula and finite
dependent limit assignment. -/
def limitRequest [Encodable Symbol] (initial : BallWitnessIndexing M)
    {n : ℕ} {context : BallContext n} {radius : ℚ≥0}
    (formula : CountableBallFormula Symbol symbolRadius
      (Fin.cons radius context))
    (indices : ∀ i : Fin n, initial.LimitIndex (context i))
    (precision : ℕ) (direction : QuantifierDirection) :
    BallWitnessRequest Symbol symbolRadius
      (initial.iterate (initial.commonStage indices)).Index where
  variableCount := n
  context := context
  quantifiedRadius := radius
  formula := formula
  indices := initial.limitAssignmentAtCommonStage indices
  precision := precision
  direction := direction

/-- The successor-stage limit index selected for one rational ball
quantifier request. -/
def limitWitness [Encodable Symbol] (initial : BallWitnessIndexing M)
    {n : ℕ} {context : BallContext n} {radius : ℚ≥0}
    (formula : CountableBallFormula Symbol symbolRadius
      (Fin.cons radius context))
    (indices : ∀ i : Fin n, initial.LimitIndex (context i))
    (precision : ℕ) (direction : QuantifierDirection) :
    initial.LimitIndex radius :=
  ⟨initial.commonStage indices + 1,
    (initial.iterate (initial.commonStage indices)).requested
      (initial.limitRequest formula indices precision direction)⟩

@[simp]
theorem limitMap_limitWitness [Encodable Symbol]
    (initial : BallWitnessIndexing M)
    {n : ℕ} {context : BallContext n} {radius : ℚ≥0}
    (formula : CountableBallFormula Symbol symbolRadius
      (Fin.cons radius context))
    (indices : ∀ i : Fin n, initial.LimitIndex (context i))
    (precision : ℕ) (direction : QuantifierDirection) :
    initial.limitMap radius
        (initial.limitWitness formula indices precision direction) =
      (initial.limitRequest formula indices precision direction).witness
        M (initial.iterate (initial.commonStage indices)).indexMap :=
  rfl

/-- Every rational ball-quantifier request over a limit assignment has a
verified witness whose index belongs to the correct limit sort. -/
theorem limitWitness_spec [Encodable Symbol]
    (initial : BallWitnessIndexing M)
    {n : ℕ} {context : BallContext n} {radius : ℚ≥0}
    (formula : CountableBallFormula Symbol symbolRadius
      (Fin.cons radius context))
    (indices : ∀ i : Fin n, initial.LimitIndex (context i))
    (precision : ℕ) (direction : QuantifierDirection) :
    match direction with
    | .supremum =>
        (((BallFormula.iSup radius formula.toBallFormula).realize M
            (initial.ambientLimitAssignment indices) : ℝ) <
          (formula.toBallFormula.realize M
            (Fin.cons
              (initial.limitMap radius
                (initial.limitWitness formula indices precision direction))
              (initial.ambientLimitAssignment indices)) : ℝ) +
            witnessError precision)
    | .infimum =>
        ((formula.toBallFormula.realize M
            (Fin.cons
              (initial.limitMap radius
                (initial.limitWitness formula indices precision direction))
              (initial.ambientLimitAssignment indices)) : ℝ) <
          ((BallFormula.iInf radius formula.toBallFormula).realize M
            (initial.ambientLimitAssignment indices) : ℝ) +
            witnessError precision) := by
  have hspec :=
    (initial.limitRequest formula indices precision direction).witness_spec
      M (initial.iterate (initial.commonStage indices)).indexMap
  have hassignment :
      (initial.limitRequest formula indices precision direction).ambientAssignment
          (initial.iterate (initial.commonStage indices)).indexMap =
        initial.ambientLimitAssignment indices := by
    funext i
    exact initial.indexMap_limitAssignmentAtCommonStage indices i
  rw [hassignment] at hspec
  simpa using hspec

end BallWitnessIndexing

end

end NormFormula.ContinuousLogic
