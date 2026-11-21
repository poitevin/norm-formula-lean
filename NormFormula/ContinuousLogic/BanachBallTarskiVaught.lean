import NormFormula.ContinuousLogic.BanachBallRationalTarskiVaught

/-!
# Tarski--Vaught for the closed ball-sorted witness limit

Uniform density of the countable rational fragment upgrades exact rational
restriction to every unrestricted typed ball formula.  In particular, the
closed witness-limit structure and its ambient structure have the same
complete typed ball theory.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u w

namespace BallWitnessIndexing

variable {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
  {M : BallStructure.{u, w} Symbol symbolRadius}

/-- Every unrestricted typed ball formula has the same value in the closed
witness-limit structure and the ambient structure on included assignments. -/
theorem ballFormula_realize_limitBallStructure_eq_ambient
    [Encodable Symbol] (initial : BallWitnessIndexing M)
    {n : ℕ} {context : BallContext n}
    (formula : BallFormula Symbol symbolRadius context)
    (assignment : BallTerm.Assignment
      initial.limitRationalBallSystem context) :
    formula.realize initial.limitBallStructure assignment =
      formula.realize M
        (initial.includeLimitBallAssignment assignment) := by
  apply Subtype.ext
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨rational, hclose⟩ :=
    formula.exists_countableBallFormula_uniformly_close (half_pos hε)
  have hclosed := hclose initial.limitBallStructure assignment
  have hambient := hclose M
    (initial.includeLimitBallAssignment assignment)
  have hrational :=
    initial.countableBallFormula_realize_limitBallStructure_eq_ambient
      rational assignment
  have hrationalReal :
      ((rational.toBallFormula.realize initial.limitBallStructure
        assignment : TruthValue) : ℝ) =
      ((rational.toBallFormula.realize M
        (initial.includeLimitBallAssignment assignment) : TruthValue) : ℝ) :=
    congrArg ((↑) : TruthValue → ℝ) hrational
  rw [Real.dist_eq]
  calc
    |(formula.realize initial.limitBallStructure assignment : ℝ) -
        (formula.realize M
          (initial.includeLimitBallAssignment assignment) : ℝ)| =
        |((formula.realize initial.limitBallStructure assignment : ℝ) -
            (rational.toBallFormula.realize initial.limitBallStructure
              assignment : ℝ)) +
          ((rational.toBallFormula.realize M
              (initial.includeLimitBallAssignment assignment) : ℝ) -
            (formula.realize M
              (initial.includeLimitBallAssignment assignment) : ℝ))| := by
          rw [hrationalReal]
          ring_nf
    _ ≤
        |(formula.realize initial.limitBallStructure assignment : ℝ) -
          (rational.toBallFormula.realize initial.limitBallStructure
            assignment : ℝ)| +
        |(rational.toBallFormula.realize M
            (initial.includeLimitBallAssignment assignment) : ℝ) -
          (formula.realize M
            (initial.includeLimitBallAssignment assignment) : ℝ)| :=
      abs_add_le _ _
    _ ≤ ε := by
      have hclosed' :
          |(formula.realize initial.limitBallStructure assignment : ℝ) -
            (rational.toBallFormula.realize initial.limitBallStructure
              assignment : ℝ)| < ε / 2 := by
        simpa only [abs_sub_comm] using hclosed
      linarith

/-- The closed witness-limit structure and the ambient structure agree on
every sentence of the unrestricted typed ball language. -/
theorem limitBallStructure_sameCompleteTheory_ambient
    [Encodable Symbol] (initial : BallWitnessIndexing M) :
    BallSameCompleteTheory initial.limitBallStructure M := by
  intro sentence
  let emptyAssignment : BallTerm.Assignment
      initial.limitRationalBallSystem (Fin.elim0 : BallContext 0) :=
    fun i : Fin 0 ↦ nomatch i
  have h := initial.ballFormula_realize_limitBallStructure_eq_ambient
    sentence emptyAssignment
  have hempty : initial.includeLimitBallAssignment emptyAssignment =
      (fun i : Fin 0 ↦ nomatch i) := by
    funext i
    exact Fin.elim0 i
  simpa only [BallSentence.value, emptyAssignment, hempty] using h

end BallWitnessIndexing

end

end NormFormula.ContinuousLogic
