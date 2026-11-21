import NormFormula.ContinuousLogic.BanachBallReducedProduct
import NormFormula.ContinuousLogic.BanachBallTerm

/-!
# Łoś computation for rational-ball terms

Evaluation of a typed ball term on completed classes of sequence
representatives is the completed class of its coordinatewise evaluations.
The proof is structural and uses the representative computation laws for the
five lifted Banach operations.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u

namespace BallTerm

variable (S : RationalBallSystem.{u})

/-- A context assignment by sequence representatives, before passing to the
completed reduced balls. -/
abbrev ReducedAssignment {n : ℕ} (context : BallContext n) :=
  ∀ i : Fin n, ReducedSequence (S.reducedBound (context i))

/-- Embed an assignment of sequence representatives into the completed
reduced ball system. -/
def completedAssignment {n : ℕ} {context : BallContext n}
    (assignment : ReducedAssignment S context) :
    Assignment S.reducedProduct context :=
  fun i ↦ ReducedProduct.completedMk (S.reducedBound (context i)) (assignment i)

/-- Evaluate a sequence assignment at one coordinate. -/
def coordinateAssignment {n : ℕ} {context : BallContext n}
    (assignment : ReducedAssignment S context) (k : ℕ) : Assignment S context :=
  fun i ↦ assignment i k

/-- Structural term Łoś theorem: term evaluation commutes exactly with the
completed reduced-product representative embedding. -/
@[simp]
theorem realize_reducedProduct {n : ℕ} {context : BallContext n} {r : ℚ≥0}
    (term : BallTerm context r) (assignment : ReducedAssignment S context) :
    term.realize S.reducedProduct (completedAssignment S assignment) =
      ReducedProduct.completedMk (S.reducedBound r)
        (fun k ↦ term.realize S (coordinateAssignment S assignment k)) := by
  induction term with
  | «variable» i => rfl
  | inclusion h term induction =>
      rw [realize_inclusion, induction, RationalBallSystem.reducedProduct_inclusion_mk]
      rfl
  | zero radius => rfl
  | neg term induction =>
      rw [realize_neg, induction, RationalBallSystem.reducedProduct_neg_mk]
      rfl
  | add left right leftInduction rightInduction =>
      rw [realize_add, leftInduction, rightInduction,
        RationalBallSystem.reducedProduct_add_mk]
      rfl
  | smul q term induction =>
      rw [realize_smul, induction, RationalBallSystem.reducedProduct_smul_mk]
      rfl

/-- The diagonal embedding preserves the value of every typed ball term. -/
@[simp]
theorem realize_reducedConst {n : ℕ} {context : BallContext n} {r : ℚ≥0}
    (term : BallTerm context r) (assignment : Assignment S context) :
    term.realize S.reducedProduct
        (fun i ↦ S.reducedConst (context i) (assignment i)) =
      S.reducedConst r (term.realize S assignment) := by
  let sequences : ReducedAssignment S context := fun i _ ↦ assignment i
  have h := realize_reducedProduct S term sequences
  simpa only [sequences, completedAssignment, coordinateAssignment,
    RationalBallSystem.reducedConst] using h

end BallTerm

end


end NormFormula.ContinuousLogic
