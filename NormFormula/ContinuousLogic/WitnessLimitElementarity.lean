import NormFormula.ContinuousLogic.RationalTarskiVaught

/-!
# Elementarity of the closed witness-limit structure

Uniform density of rational formulae upgrades the exact rational
Tarski--Vaught theorem to preservation of every unrestricted formula.  In
particular, the closed witness-limit structure and its ambient structure have
the same value for every sentence.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.parameterPseudoMetricSpace MultiStructure.rowNonempty
  MultiStructure.parameterNonempty

universe u v w

namespace WitnessIndexing

variable {Symbol : Type w} {M : MultiStructure.{u, v, w} Symbol}

/-- Inclusion of the closed witness-limit structure preserves every
unrestricted continuous formula. -/
theorem formula_realize_limitStructure_eq_ambient [Encodable Symbol]
    (initial : WitnessIndexing M)
    [Nonempty initial.RowIndex] [Nonempty initial.ParameterIndex]
    {rowVars parameterVars : ℕ}
    (formula : MultiFormula Symbol rowVars parameterVars)
    (rows : Fin rowVars → (initial.limitStructure).Row)
    (parameters : Fin parameterVars → (initial.limitStructure).Parameter) :
    formula.realize (initial.limitStructure) rows parameters =
      formula.realize M
        (fun i => initial.limitRowInclusion (rows i))
        (fun i => initial.limitParameterInclusion (parameters i)) := by
  apply Subtype.ext
  have hclose : ∀ ε : ℝ, 0 < ε →
      |(formula.realize (initial.limitStructure) rows parameters : ℝ) -
        (formula.realize M
          (fun i => initial.limitRowInclusion (rows i))
          (fun i => initial.limitParameterInclusion (parameters i)) : ℝ)| < ε := by
    intro ε hε
    obtain ⟨rational, hrational, happroximation⟩ :=
      formula.exists_rationalFormula_uniformly_close (half_pos hε)
    let rationalFormula : CountableFormula Symbol rowVars parameterVars :=
      ⟨rational, hrational⟩
    have hrationalEq :=
      WitnessIndexing.CountableFormula.realize_limitStructure_eq_ambient
        initial rationalFormula rows parameters
    have hrestricted := happroximation
      (initial.limitStructure) rows parameters
    have hambient := happroximation M
      (fun i => initial.limitRowInclusion (rows i))
      (fun i => initial.limitParameterInclusion (parameters i))
    change
      |(rationalFormula.toMultiFormula.realize
          (initial.limitStructure) rows parameters : ℝ) -
        (formula.realize (initial.limitStructure) rows parameters : ℝ)| <
          ε / 2 at hrestricted
    change
      |(rationalFormula.toMultiFormula.realize M
          (fun i => initial.limitRowInclusion (rows i))
          (fun i => initial.limitParameterInclusion (parameters i)) : ℝ) -
        (formula.realize M
          (fun i => initial.limitRowInclusion (rows i))
          (fun i => initial.limitParameterInclusion (parameters i)) : ℝ)| <
          ε / 2 at hambient
    calc
      |(formula.realize (initial.limitStructure) rows parameters : ℝ) -
          (formula.realize M
            (fun i => initial.limitRowInclusion (rows i))
            (fun i => initial.limitParameterInclusion (parameters i)) : ℝ)| ≤
          |(formula.realize (initial.limitStructure) rows parameters : ℝ) -
            (rationalFormula.toMultiFormula.realize
              (initial.limitStructure) rows parameters : ℝ)| +
          |(rationalFormula.toMultiFormula.realize
              (initial.limitStructure) rows parameters : ℝ) -
            (formula.realize M
              (fun i => initial.limitRowInclusion (rows i))
              (fun i => initial.limitParameterInclusion (parameters i)) : ℝ)| :=
        abs_sub_le _ _ _
      _ = |(rationalFormula.toMultiFormula.realize
              (initial.limitStructure) rows parameters : ℝ) -
            (formula.realize (initial.limitStructure) rows parameters : ℝ)| +
          |(rationalFormula.toMultiFormula.realize M
              (fun i => initial.limitRowInclusion (rows i))
              (fun i => initial.limitParameterInclusion (parameters i)) : ℝ) -
            (formula.realize M
              (fun i => initial.limitRowInclusion (rows i))
              (fun i => initial.limitParameterInclusion (parameters i)) : ℝ)| := by
        rw [abs_sub_comm]
        rw [hrationalEq]
      _ < ε := by
        calc
          _ < ε / 2 + ε / 2 := add_lt_add hrestricted hambient
          _ = ε := by ring
  have habs :
      |(formula.realize (initial.limitStructure) rows parameters : ℝ) -
        (formula.realize M
          (fun i => initial.limitRowInclusion (rows i))
          (fun i => initial.limitParameterInclusion (parameters i)) : ℝ)| = 0 := by
    apply le_antisymm
    · apply le_of_forall_pos_le_add
      intro ε hε
      simpa using (hclose ε hε).le
    · exact abs_nonneg _
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

/-- The closed witness-limit structure has exactly the ambient value for every
sentence. -/
theorem sentence_value_limitStructure_eq_ambient [Encodable Symbol]
    (initial : WitnessIndexing M)
    [Nonempty initial.RowIndex] [Nonempty initial.ParameterIndex]
    (sentence : MultiSentence Symbol) :
    sentence.value (initial.limitStructure) = sentence.value M := by
  change sentence.realize (initial.limitStructure) Fin.elim0 Fin.elim0 =
    sentence.realize M Fin.elim0 Fin.elim0
  have h := initial.formula_realize_limitStructure_eq_ambient
    sentence Fin.elim0 Fin.elim0
  have hrow :
      (fun i : Fin 0 => initial.limitRowInclusion
        (Fin.elim0 i : (initial.limitStructure).Row)) =
        (Fin.elim0 : Fin 0 → M.Row) := by
    funext i
    exact Fin.elim0 i
  have hparameter :
      (fun i : Fin 0 => initial.limitParameterInclusion
        (Fin.elim0 i : (initial.limitStructure).Parameter)) =
        (Fin.elim0 : Fin 0 → M.Parameter) := by
    funext i
    exact Fin.elim0 i
  rw [hrow, hparameter] at h
  exact h

/-- The closed witness-limit structure and the ambient structure have the
same complete theory. -/
theorem limitStructure_sameCompleteTheory [Encodable Symbol]
    (initial : WitnessIndexing M)
    [Nonempty initial.RowIndex] [Nonempty initial.ParameterIndex] :
    MultiSameCompleteTheory (initial.limitStructure) M :=
  initial.sentence_value_limitStructure_eq_ambient

end WitnessIndexing

end

end NormFormula.ContinuousLogic
