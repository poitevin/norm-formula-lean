import NormFormula.ContinuousLogic.FormulaDensity

/-!
# Approximate witnesses for continuous quantifiers

Suprema and infima of truth-value families need not be attained.  For the
continuous Tarski--Vaught construction it is enough to adjoin witnesses that
approach the quantified value within each positive tolerance.  This file
proves the generic order-theoretic choices and specializes them to all four
quantifiers of `MultiFormula`.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

/-- A nonempty truth-value family has an element within any positive error
below its supremum. -/
theorem exists_iSup_approximation {ι : Type*} [Nonempty ι]
    (values : ι → TruthValue) {ε : ℝ} (hε : 0 < ε) :
    ∃ i, ((↑(⨆ j, values j) : ℝ) < (values i : ℝ) + ε) := by
  have hcoe : (↑(⨆ j, values j) : ℝ) = ⨆ j, (values j : ℝ) :=
    Set.Icc.coe_iSup zero_le_one
  have hlt : (↑(⨆ j, values j) : ℝ) - ε < ⨆ j, (values j : ℝ) := by
    rw [← hcoe]
    exact sub_lt_self _ hε
  obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup hlt
  exact ⟨i, sub_lt_iff_lt_add.mp hi⟩

/-- A nonempty truth-value family has an element within any positive error
above its infimum. -/
theorem exists_iInf_approximation {ι : Type*} [Nonempty ι]
    (values : ι → TruthValue) {ε : ℝ} (hε : 0 < ε) :
    ∃ i, (values i : ℝ) < (↑(⨅ j, values j) : ℝ) + ε := by
  have hcoe : (↑(⨅ j, values j) : ℝ) = ⨅ j, (values j : ℝ) :=
    Set.Icc.coe_iInf zero_le_one
  have hlt : (⨅ j, (values j : ℝ)) < (↑(⨅ j, values j) : ℝ) + ε := by
    rw [hcoe]
    exact lt_add_of_pos_right _ hε
  exact exists_lt_of_ciInf_lt hlt

namespace MultiFormula

/-- A row can approximate a row-supremum value from below at any positive
tolerance. -/
theorem exists_row_iSup_approximation
    {Symbol : Type*} {rowVars parameterVars : ℕ}
    (formula : MultiFormula Symbol (rowVars + 1) parameterVars)
    (M : MultiStructure Symbol)
    (rows : Fin rowVars → M.Row)
    (parameters : Fin parameterVars → M.Parameter)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : M.Row,
      (((MultiFormula.iSupRow formula).realize M rows parameters : ℝ) <
        (formula.realize M (Fin.cons x rows) parameters : ℝ) + ε) := by
  letI := M.rowNonempty
  exact exists_iSup_approximation _ hε

/-- A row can approximate a row-infimum value from above at any positive
tolerance. -/
theorem exists_row_iInf_approximation
    {Symbol : Type*} {rowVars parameterVars : ℕ}
    (formula : MultiFormula Symbol (rowVars + 1) parameterVars)
    (M : MultiStructure Symbol)
    (rows : Fin rowVars → M.Row)
    (parameters : Fin parameterVars → M.Parameter)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : M.Row,
      ((formula.realize M (Fin.cons x rows) parameters : ℝ) <
        ((MultiFormula.iInfRow formula).realize M rows parameters : ℝ) + ε) := by
  letI := M.rowNonempty
  exact exists_iInf_approximation _ hε

/-- A parameter can approximate a parameter-supremum value from below at any
positive tolerance. -/
theorem exists_parameter_iSup_approximation
    {Symbol : Type*} {rowVars parameterVars : ℕ}
    (formula : MultiFormula Symbol rowVars (parameterVars + 1))
    (M : MultiStructure Symbol)
    (rows : Fin rowVars → M.Row)
    (parameters : Fin parameterVars → M.Parameter)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : M.Parameter,
      (((MultiFormula.iSupParameter formula).realize M rows parameters : ℝ) <
        (formula.realize M rows (Fin.cons y parameters) : ℝ) + ε) := by
  letI := M.parameterNonempty
  exact exists_iSup_approximation _ hε

/-- A parameter can approximate a parameter-infimum value from above at any
positive tolerance. -/
theorem exists_parameter_iInf_approximation
    {Symbol : Type*} {rowVars parameterVars : ℕ}
    (formula : MultiFormula Symbol rowVars (parameterVars + 1))
    (M : MultiStructure Symbol)
    (rows : Fin rowVars → M.Row)
    (parameters : Fin parameterVars → M.Parameter)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : M.Parameter,
      ((formula.realize M rows (Fin.cons y parameters) : ℝ) <
        ((MultiFormula.iInfParameter formula).realize M rows parameters : ℝ) + ε) := by
  letI := M.parameterNonempty
  exact exists_iInf_approximation _ hε

end MultiFormula

end

end NormFormula.ContinuousLogic
