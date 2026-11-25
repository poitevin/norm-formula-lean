import NormFormula.ContinuousLogic.BanachBallFormulaContinuity

/-!
# Supremum restriction for rational ball formulae

Canonical assignments from the countable stage limit are dense in every
finite dependent assignment space.  On such assignments, the easy
supremum inequality follows from carrier inclusion, while the reverse
inequality uses the successor-stage approximate witness at arbitrary
precision.  Continuity extends equality to all completed assignments.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Function Set

universe u w

namespace BallWitnessIndexing

variable {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
  {M : BallStructure.{u, w} Symbol symbolRadius}

/-- The canonical closed-carrier assignment associated to a finite tuple of
limit indices. -/
def limitBallAssignmentPoint [Encodable Symbol]
    (initial : BallWitnessIndexing M)
    {n : ℕ} {context : BallContext n}
    (indices : ∀ i : Fin n, initial.LimitIndex (context i)) :
    BallTerm.Assignment initial.limitRationalBallSystem context :=
  fun i ↦ initial.limitPoint (context i) (indices i)


/-- Canonical limit assignments are dense in each finite dependent closed
assignment space. -/
theorem denseRange_limitBallAssignmentPoint [Encodable Symbol]
    (initial : BallWitnessIndexing M)
    {n : ℕ} (context : BallContext n) :
    DenseRange (initial.limitBallAssignmentPoint :
      (∀ i : Fin n, initial.LimitIndex (context i)) →
        BallTerm.Assignment initial.limitRationalBallSystem context) :=
  DenseRange.piMap fun i ↦ initial.denseRange_limitPoint (context i)

/-- Inclusion of finite dependent closed assignments into the ambient
structure is continuous. -/
theorem continuous_includeLimitBallAssignment [Encodable Symbol]
    (initial : BallWitnessIndexing M)
    {n : ℕ} (context : BallContext n) :
    Continuous (initial.includeLimitBallAssignment :
      BallTerm.Assignment initial.limitRationalBallSystem context →
        BallTerm.Assignment M.toRationalBallSystem context) := by
  apply continuous_pi
  intro i
  exact continuous_subtype_val.comp (continuous_apply i)


/-- A rational ball supremum is preserved by the closed limit structure once
its child formula is preserved. -/
theorem realize_iSup_limitBallStructure_eq_ambient [Encodable Symbol]
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
    (BallFormula.iSup radius formula.toBallFormula).realize
        initial.limitBallStructure assignment =
      (BallFormula.iSup radius formula.toBallFormula).realize M
        (initial.includeLimitBallAssignment assignment) := by
  let restricted :
      BallTerm.Assignment initial.limitRationalBallSystem context →
        TruthValue :=
    (BallFormula.iSup radius formula.toBallFormula).realize
      initial.limitBallStructure
  let ambient :
      BallTerm.Assignment initial.limitRationalBallSystem context →
        TruthValue :=
    fun current ↦
      (BallFormula.iSup radius formula.toBallFormula).realize M
        (initial.includeLimitBallAssignment current)
  have hrestricted : Continuous restricted :=
    (BallFormula.iSup radius formula.toBallFormula).realize_continuous
      initial.limitBallStructure
  have hambient : Continuous ambient :=
    ((BallFormula.iSup radius formula.toBallFormula).realize_continuous M).comp
      (initial.continuous_includeLimitBallAssignment context)
  have hequal : restricted = ambient :=
    (initial.denseRange_limitBallAssignmentPoint context).equalizer
      hrestricted hambient (by
        funext indices
        apply le_antisymm
        · refine iSup_le fun x ↦ ?_
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
            formula.toBallFormula.realize M
                (initial.includeLimitBallAssignment
                  (Fin.cons x (initial.limitBallAssignmentPoint indices))) =
              formula.toBallFormula.realize M
                (Fin.cons (initial.limitBallInclusion radius x)
                  (initial.ambientLimitAssignment indices)) :=
                congrArg (formula.toBallFormula.realize M) hcons
            _ ≤ (BallFormula.iSup radius formula.toBallFormula).realize M
                  (initial.ambientLimitAssignment indices) :=
              le_iSup
                (fun z : M.Ball radius ↦
                  formula.toBallFormula.realize M
                    (Fin.cons z (initial.ambientLimitAssignment indices)))
                (initial.limitBallInclusion radius x)
            _ = (ambient ∘ initial.limitBallAssignmentPoint) indices := rfl
        · rw [← Subtype.coe_le_coe]
          apply le_of_forall_pos_le_add
          intro ε hε
          obtain ⟨precision, hprecision⟩ := exists_nat_one_div_lt hε
          let witness := initial.limitWitness formula indices precision .supremum
          have hspec := initial.limitWitness_spec formula indices precision
            .supremum
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
          have hwitness_le :
              formula.toBallFormula.realize initial.limitBallStructure
                  (Fin.cons (initial.limitPoint radius witness)
                    (initial.limitBallAssignmentPoint indices)) ≤
                (BallFormula.iSup radius formula.toBallFormula).realize
                  initial.limitBallStructure
                  (initial.limitBallAssignmentPoint indices) := by
            change _ ≤ ⨆ x,
              formula.toBallFormula.realize initial.limitBallStructure
                (Fin.cons x (initial.limitBallAssignmentPoint indices))
            exact le_iSup
              (fun x : initial.LimitCarrier radius ↦
                formula.toBallFormula.realize initial.limitBallStructure
                  (Fin.cons x (initial.limitBallAssignmentPoint indices)))
              (initial.limitPoint radius witness)
          have hwitness_le_real :=
            (Subtype.coe_le_coe.mpr hwitness_le :
              (formula.toBallFormula.realize initial.limitBallStructure
                  (Fin.cons (initial.limitPoint radius witness)
                    (initial.limitBallAssignmentPoint indices)) : ℝ) ≤
                ((BallFormula.iSup radius formula.toBallFormula).realize
                  initial.limitBallStructure
                  (initial.limitBallAssignmentPoint indices) : ℝ))
          have hprecision' : witnessError precision < ε := by
            simpa [witnessError] using hprecision
          exact (calc
            ((BallFormula.iSup radius formula.toBallFormula).realize M
                (initial.ambientLimitAssignment indices) : ℝ) <
                (formula.toBallFormula.realize M
                  (Fin.cons (initial.limitMap radius witness)
                    (initial.ambientLimitAssignment indices)) : ℝ) +
                  witnessError precision := hspec
            _ = (formula.toBallFormula.realize initial.limitBallStructure
                  (Fin.cons (initial.limitPoint radius witness)
                    (initial.limitBallAssignmentPoint indices)) : ℝ) +
                  witnessError precision := by
              exact congrArg (fun value : TruthValue ↦ (value : ℝ) +
                witnessError precision) hchild'.symm
            _ ≤ ((BallFormula.iSup radius formula.toBallFormula).realize
                  initial.limitBallStructure
                  (initial.limitBallAssignmentPoint indices) : ℝ) +
                  witnessError precision :=
              by simpa [add_comm] using
                add_le_add_right hwitness_le_real (witnessError precision)
            _ < ((BallFormula.iSup radius formula.toBallFormula).realize
                  initial.limitBallStructure
                  (initial.limitBallAssignmentPoint indices) : ℝ) + ε :=
              by simpa [add_comm] using
                add_lt_add_left hprecision'
                  ((BallFormula.iSup radius formula.toBallFormula).realize
                    initial.limitBallStructure
                    (initial.limitBallAssignmentPoint indices) : ℝ)).le)
  exact congrFun hequal assignment

end BallWitnessIndexing

end

end NormFormula.ContinuousLogic
