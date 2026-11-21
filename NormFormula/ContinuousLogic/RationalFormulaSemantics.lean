import NormFormula.ContinuousLogic.RationalConnectiveDensity

/-!
# Semantics of rational connective substitution

This file connects the rational lattice approximation theorem to the
countable formula language.  Substituting rational formulae for the
coordinates of a lattice code and then evaluating is exactly the same as
applying the bounded connective denoted by the code to the input
evaluations.  Consequently every unrestricted continuous connective applied
to rational input formulae has a rational formula approximation with a
uniform semantic error bound, simultaneously in every structure and under
every assignment.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open scoped Topology

namespace RationalLatticeCode

@[simp]
theorem finCases_two_one {α : Sort*} (first second : α) :
    Fin.cases first (Fin.cases second Fin.elim0) (1 : Fin 2) = second :=
  rfl

/-- Evaluating a substituted lattice code computes its recursively bounded
interpretation on the evaluations of the input formulae. -/
theorem realize_toMultiFormula_instantiate_eq_recursiveBoundedValue
    {Symbol : Type*} {arity rowVars parameterVars : ℕ}
    (code : RationalLatticeCode arity)
    (inputs : Fin arity → RationalFormula Symbol)
    (hinputs : ∀ coordinate,
      (inputs coordinate).WellFormed rowVars parameterVars)
    (hcode : (code.instantiate inputs).WellFormed rowVars parameterVars)
    (M : MultiStructure Symbol)
    (rows : Fin rowVars → M.Row)
    (parameters : Fin parameterVars → M.Parameter) :
    ((code.instantiate inputs).toMultiFormula rowVars parameterVars hcode).realize
        M rows parameters =
      code.recursiveBoundedValue (fun coordinate =>
        ((inputs coordinate).toMultiFormula rowVars parameterVars
          (hinputs coordinate)).realize M rows parameters) := by
  induction code with
  | constant value => rfl
  | affine coordinate bias slope =>
      simp [instantiate, RationalFormula.toMultiFormula, MultiFormula.realize,
        recursiveBoundedValue, rationalClippedAffine₂, clampTruthValue]
  | min left right leftInduction rightInduction =>
      apply Subtype.ext
      simp [instantiate, RationalFormula.toMultiFormula,
        MultiFormula.realize, recursiveBoundedValue, rationalMinConnective,
        Fin.cases_zero, leftInduction hcode.1, rightInduction hcode.2]
  | max left right leftInduction rightInduction =>
      apply Subtype.ext
      simp [instantiate, RationalFormula.toMultiFormula,
        MultiFormula.realize, recursiveBoundedValue, rationalMaxConnective,
        Fin.cases_zero, leftInduction hcode.1, rightInduction hcode.2]

/-- Evaluating a substituted lattice code is exactly application of its
bounded connective to the input evaluations. -/
theorem realize_toMultiFormula_instantiate_eq_toConnective
    {Symbol : Type*} {arity rowVars parameterVars : ℕ}
    (code : RationalLatticeCode arity)
    (inputs : Fin arity → RationalFormula Symbol)
    (hinputs : ∀ coordinate,
      (inputs coordinate).WellFormed rowVars parameterVars)
    (hcode : (code.instantiate inputs).WellFormed rowVars parameterVars)
    (M : MultiStructure Symbol)
    (rows : Fin rowVars → M.Row)
    (parameters : Fin parameterVars → M.Parameter) :
    ((code.instantiate inputs).toMultiFormula rowVars parameterVars hcode).realize
        M rows parameters =
      code.toConnective (fun coordinate =>
        ((inputs coordinate).toMultiFormula rowVars parameterVars
          (hinputs coordinate)).realize M rows parameters) := by
  rw [realize_toMultiFormula_instantiate_eq_recursiveBoundedValue
    code inputs hinputs hcode M rows parameters]
  exact code.recursiveBoundedValue_eq_boundedValue _

end RationalLatticeCode

namespace Connective

/-- Applying any bounded continuous connective to rational input formulae is
uniformly approximated by a rational formula, in every structure and under
every assignment. -/
theorem exists_rationalFormula_uniformly_close_of_inputs
    {Symbol : Type*} {arity rowVars parameterVars : ℕ}
    (connective : Connective arity)
    (inputs : Fin arity → RationalFormula Symbol)
    (hinputs : ∀ coordinate,
      (inputs coordinate).WellFormed rowVars parameterVars)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ formula : RationalFormula Symbol,
      ∃ hformula : formula.WellFormed rowVars parameterVars,
        ∀ (M : MultiStructure Symbol)
          (rows : Fin rowVars → M.Row)
          (parameters : Fin parameterVars → M.Parameter),
          |((formula.toMultiFormula rowVars parameterVars hformula).realize
              M rows parameters : ℝ) -
            (connective (fun coordinate =>
              ((inputs coordinate).toMultiFormula rowVars parameterVars
                (hinputs coordinate)).realize M rows parameters) : ℝ)| < ε := by
  obtain ⟨code, hcode⟩ :=
    connective.exists_rationalLatticeCode_uniformly_close hε
  refine ⟨code.instantiate inputs,
    code.wellFormed_instantiate inputs hinputs, ?_⟩
  intro M rows parameters
  rw [code.realize_toMultiFormula_instantiate_eq_toConnective inputs hinputs]
  exact hcode _

end Connective

end

end NormFormula.ContinuousLogic
