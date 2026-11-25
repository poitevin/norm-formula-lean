import NormFormula.ContinuousLogic.MultiPredicate

/-!
# Approximate witnesses for continuous quantifiers

Suprema and infima of truth-value families need not be attained.  For the
continuous Tarski--Vaught construction it is enough to adjoin witnesses that
approach the quantified value within each positive tolerance.  This file
proves the order-theoretic choices.
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


end MultiFormula

end

end NormFormula.ContinuousLogic
