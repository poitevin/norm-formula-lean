import Mathlib.Tactic.FinCases
import NormFormula.ContinuousLogic.BanachBallInfRestriction

/-!
# Rational Tarski--Vaught for the closed ball-sorted limit

The atomic, constant, connective, supremum, and infimum restriction lemmas
are assembled by recursion over a well-typed raw rational ball-formula code.
Consequently every formula in the countable rational fragment has exactly
its ambient value on every included closed-carrier assignment.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u w

namespace RationalBallFormulaCode

/-- An elaborated rational formula code has the same value in the closed
limit structure and the ambient structure. -/
theorem realize_limitBallStructure_eq_ambient
    {Symbol : Type w} [Encodable Symbol]
    {symbolRadius : Symbol → ℚ≥0}
    {M : BallStructure.{u, w} Symbol symbolRadius}
    (initial : BallWitnessIndexing M)
    {n : ℕ} {context : BallContext n}
    (code : RationalBallFormulaCode Symbol)
    {formula : BallFormula Symbol symbolRadius context}
    (helaborate : code.elaborate symbolRadius context = some formula)
    (assignment : BallTerm.Assignment
      initial.limitRationalBallSystem context) :
    formula.realize initial.limitBallStructure assignment =
      formula.realize M (initial.includeLimitBallAssignment assignment) := by
  induction code generalizing n context formula with
  | distance radius left right =>
      cases hleft : left.elaborateAt context radius with
      | none =>
          simp [elaborate, hleft] at helaborate
      | some leftTyped =>
          cases hright : right.elaborateAt context radius with
          | none =>
              simp [elaborate, hleft, hright] at helaborate
          | some rightTyped =>
              simp [elaborate, hleft, hright] at helaborate
              subst formula
              exact initial.distance_realize_limitBallStructure_eq_ambient
                leftTyped rightTyped assignment
  | predicate symbol term =>
      cases hterm : term.elaborateAt context (symbolRadius symbol) with
      | none =>
          simp [elaborate, hterm] at helaborate
      | some typed =>
          simp [elaborate, hterm] at helaborate
          subst formula
          exact initial.predicate_realize_limitBallStructure_eq_ambient
            symbol typed assignment
  | constant value =>
      simp [elaborate] at helaborate
      subst formula
      exact initial.constant_realize_limitBallStructure_eq_ambient
        (clampTruthValue value) assignment
  | affine₂ bias first second left right leftInduction rightInduction =>
      cases hleft : left.elaborate symbolRadius context with
      | none =>
          simp [elaborate, hleft] at helaborate
      | some leftFormula =>
          cases hright : right.elaborate symbolRadius context with
          | none =>
              simp [elaborate, hleft, hright] at helaborate
          | some rightFormula =>
              simp [elaborate, hleft, hright] at helaborate
              subst formula
              apply initial.connective_realize_limitBallStructure_eq_ambient
              intro i
              fin_cases i
              · exact leftInduction hleft assignment
              · exact rightInduction hright assignment
  | min left right leftInduction rightInduction =>
      cases hleft : left.elaborate symbolRadius context with
      | none =>
          simp [elaborate, hleft] at helaborate
      | some leftFormula =>
          cases hright : right.elaborate symbolRadius context with
          | none =>
              simp [elaborate, hleft, hright] at helaborate
          | some rightFormula =>
              simp [elaborate, hleft, hright] at helaborate
              subst formula
              apply initial.connective_realize_limitBallStructure_eq_ambient
              intro i
              fin_cases i
              · exact leftInduction hleft assignment
              · exact rightInduction hright assignment
  | max left right leftInduction rightInduction =>
      cases hleft : left.elaborate symbolRadius context with
      | none =>
          simp [elaborate, hleft] at helaborate
      | some leftFormula =>
          cases hright : right.elaborate symbolRadius context with
          | none =>
              simp [elaborate, hleft, hright] at helaborate
          | some rightFormula =>
              simp [elaborate, hleft, hright] at helaborate
              subst formula
              apply initial.connective_realize_limitBallStructure_eq_ambient
              intro i
              fin_cases i
              · exact leftInduction hleft assignment
              · exact rightInduction hright assignment
  | iSup radius child induction =>
      cases hchild : child.elaborate symbolRadius (Fin.cons radius context) with
      | none =>
          simp [elaborate, hchild] at helaborate
      | some childFormula =>
          simp [elaborate, hchild] at helaborate
          subst formula
          let rationalChild : CountableBallFormula Symbol symbolRadius
              (Fin.cons radius context) :=
            ⟨child, childFormula, hchild⟩
          have hto : rationalChild.toBallFormula = childFormula :=
            rationalChild.toBallFormula_eq_of_elaborate hchild
          have hquant := initial.realize_iSup_limitBallStructure_eq_ambient
            radius rationalChild (by
              intro current
              simpa only [hto] using
                induction hchild current) assignment
          simpa only [hto] using hquant
  | iInf radius child induction =>
      cases hchild : child.elaborate symbolRadius (Fin.cons radius context) with
      | none =>
          simp [elaborate, hchild] at helaborate
      | some childFormula =>
          simp [elaborate, hchild] at helaborate
          subst formula
          let rationalChild : CountableBallFormula Symbol symbolRadius
              (Fin.cons radius context) :=
            ⟨child, childFormula, hchild⟩
          have hto : rationalChild.toBallFormula = childFormula :=
            rationalChild.toBallFormula_eq_of_elaborate hchild
          have hquant := initial.realize_iInf_limitBallStructure_eq_ambient
            radius rationalChild (by
              intro current
              simpa only [hto] using
                induction hchild current) assignment
          simpa only [hto] using hquant

end RationalBallFormulaCode

namespace BallWitnessIndexing

variable {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
  {M : BallStructure.{u, w} Symbol symbolRadius}

/-- Every formula in the countable rational ball fragment has exactly its
ambient value on included closed-carrier assignments. -/
theorem countableBallFormula_realize_limitBallStructure_eq_ambient
    [Encodable Symbol] (initial : BallWitnessIndexing M)
    {n : ℕ} {context : BallContext n}
    (formula : CountableBallFormula Symbol symbolRadius context)
    (assignment : BallTerm.Assignment
      initial.limitRationalBallSystem context) :
    formula.toBallFormula.realize initial.limitBallStructure assignment =
      formula.toBallFormula.realize M
        (initial.includeLimitBallAssignment assignment) :=
  formula.1.realize_limitBallStructure_eq_ambient initial
    formula.elaborate_toBallFormula assignment

end BallWitnessIndexing

end

end NormFormula.ContinuousLogic
