import NormFormula.ContinuousLogic.BanachBallSupRestriction

/-!
# Infimum restriction for rational ball formulae

This is the order-dual Tarski--Vaught argument to rational supremum
restriction.  Approximate infimum witnesses give one comparison on canonical
limit assignments, inclusion gives the other, and continuity plus density
extends equality to every completed assignment.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Function Set

universe u w

namespace BallWitnessIndexing

variable {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
  {M : BallStructure.{u, w} Symbol symbolRadius}

/-- A rational ball infimum is preserved by the closed limit structure once
its child formula is preserved. -/
theorem realize_iInf_limitBallStructure_eq_ambient [Encodable Symbol]
    (initial : BallWitnessIndexing M)
    {n : ℕ} {context : BallContext n} (radius : ℚ≥0)
    (formula : CountableBallFormula Symbol symbolRadius
      (Fin.cons radius context))
    (hformula : ∀ assignment : BallTerm.Assignment
      initial.limitRationalBallSystem (Fin.cons radius context),
      formula.toBallFormula.realize initial.limitBallStructure assignment =
        formula.toBallFormula.realize M
          (initial.includeLimitBallAssignment assignment))
    (assignment : BallTerm.Assignment
      initial.limitRationalBallSystem context) :
    (BallFormula.iInf radius formula.toBallFormula).realize
        initial.limitBallStructure assignment =
      (BallFormula.iInf radius formula.toBallFormula).realize M
        (initial.includeLimitBallAssignment assignment) := by
  let restricted :
      BallTerm.Assignment initial.limitRationalBallSystem context →
        TruthValue :=
    (BallFormula.iInf radius formula.toBallFormula).realize
      initial.limitBallStructure
  let ambient :
      BallTerm.Assignment initial.limitRationalBallSystem context →
        TruthValue :=
    fun current ↦
      (BallFormula.iInf radius formula.toBallFormula).realize M
        (initial.includeLimitBallAssignment current)
  have hrestricted : Continuous restricted :=
    (BallFormula.iInf radius formula.toBallFormula).realize_continuous
      initial.limitBallStructure
  have hambient : Continuous ambient :=
    ((BallFormula.iInf radius formula.toBallFormula).realize_continuous M).comp
      (initial.continuous_includeLimitBallAssignment context)
  have hequal : restricted = ambient :=
    (initial.denseRange_limitBallAssignmentPoint context).equalizer
      hrestricted hambient (by
        funext indices
        apply le_antisymm
        · rw [← Subtype.coe_le_coe]
          apply le_of_forall_pos_le_add
          intro ε hε
          obtain ⟨precision, hprecision⟩ := exists_nat_one_div_lt hε
          let witness := initial.limitWitness formula indices precision .infimum
          have hspec := initial.limitWitness_spec formula indices precision
            .infimum
          have hchild := hformula
            (Fin.cons (initial.limitPoint radius witness)
              (initial.limitBallAssignmentPoint indices))
          have hchild' :
              formula.toBallFormula.realize initial.limitBallStructure
                  (Fin.cons (initial.limitPoint radius witness)
                    (initial.limitBallAssignmentPoint indices)) =
                formula.toBallFormula.realize M
                  (Fin.cons (initial.limitMap radius witness)
                    (initial.ambientLimitAssignment indices)) := by
            calc
              _ = formula.toBallFormula.realize M
                    (initial.includeLimitBallAssignment
                      (Fin.cons (initial.limitPoint radius witness)
                        (initial.limitBallAssignmentPoint indices))) := hchild
              _ = _ := by
                congr 1
                funext i
                refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
          have hinf_le :
              (BallFormula.iInf radius formula.toBallFormula).realize
                  initial.limitBallStructure
                  (initial.limitBallAssignmentPoint indices) ≤
                formula.toBallFormula.realize initial.limitBallStructure
                  (Fin.cons (initial.limitPoint radius witness)
                    (initial.limitBallAssignmentPoint indices)) := by
            change (⨅ x,
              formula.toBallFormula.realize initial.limitBallStructure
                (Fin.cons x (initial.limitBallAssignmentPoint indices))) ≤ _
            exact iInf_le
              (fun x : initial.LimitCarrier radius ↦
                formula.toBallFormula.realize initial.limitBallStructure
                  (Fin.cons x (initial.limitBallAssignmentPoint indices)))
              (initial.limitPoint radius witness)
          have hinf_le_real :=
            (Subtype.coe_le_coe.mpr hinf_le :
              ((BallFormula.iInf radius formula.toBallFormula).realize
                  initial.limitBallStructure
                  (initial.limitBallAssignmentPoint indices) : ℝ) ≤
                (formula.toBallFormula.realize initial.limitBallStructure
                  (Fin.cons (initial.limitPoint radius witness)
                    (initial.limitBallAssignmentPoint indices)) : ℝ))
          have hprecision' : witnessError precision < ε := by
            simpa [witnessError] using hprecision
          exact (calc
            ((BallFormula.iInf radius formula.toBallFormula).realize
                  initial.limitBallStructure
                  (initial.limitBallAssignmentPoint indices) : ℝ) ≤
                (formula.toBallFormula.realize initial.limitBallStructure
                  (Fin.cons (initial.limitPoint radius witness)
                    (initial.limitBallAssignmentPoint indices)) : ℝ) :=
              hinf_le_real
            _ = (formula.toBallFormula.realize M
                  (Fin.cons (initial.limitMap radius witness)
                    (initial.ambientLimitAssignment indices)) : ℝ) :=
              congrArg (fun value : TruthValue ↦ (value : ℝ)) hchild'
            _ < ((BallFormula.iInf radius formula.toBallFormula).realize M
                    (initial.ambientLimitAssignment indices) : ℝ) +
                  witnessError precision := hspec
            _ < ((BallFormula.iInf radius formula.toBallFormula).realize M
                    (initial.ambientLimitAssignment indices) : ℝ) + ε :=
              by simpa [add_comm] using
                add_lt_add_left hprecision'
                  ((BallFormula.iInf radius formula.toBallFormula).realize M
                    (initial.ambientLimitAssignment indices) : ℝ)).le
        · refine le_iInf fun x ↦ ?_
          rw [hformula]
          have hcons :
              initial.includeLimitBallAssignment
                  ((Fin.cons x (initial.limitBallAssignmentPoint indices)) :
                    BallTerm.Assignment initial.limitRationalBallSystem
                      (Fin.cons radius context)) =
                (Fin.cons (initial.limitBallInclusion radius x)
                  (initial.ambientLimitAssignment indices) :
                    BallTerm.Assignment M.toRationalBallSystem
                      (Fin.cons radius context)) := by
            funext i
            refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
          exact calc
            (ambient ∘ initial.limitBallAssignmentPoint) indices =
                (BallFormula.iInf radius formula.toBallFormula).realize M
                  (initial.ambientLimitAssignment indices) := rfl
            _ ≤ formula.toBallFormula.realize M
                  (Fin.cons (initial.limitBallInclusion radius x)
                    (initial.ambientLimitAssignment indices)) :=
              iInf_le
                (fun z : M.Ball radius ↦
                  formula.toBallFormula.realize M
                    (Fin.cons z (initial.ambientLimitAssignment indices)))
                (initial.limitBallInclusion radius x)
            _ = formula.toBallFormula.realize M
                  (initial.includeLimitBallAssignment
                    (Fin.cons x
                      (initial.limitBallAssignmentPoint indices))) :=
              congrArg (formula.toBallFormula.realize M) hcons.symm)
  exact congrFun hequal assignment

end BallWitnessIndexing

end

end NormFormula.ContinuousLogic
