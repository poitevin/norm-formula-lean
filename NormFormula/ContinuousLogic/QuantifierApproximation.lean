import NormFormula.ContinuousLogic.RationalFormulaSemantics

/-!
# Uniform-error bounds for continuous quantifiers

Supremum and infimum over any nonempty sort do not enlarge a uniform error
between truth-value families.  This file proves the underlying order-theoretic
lemmas and specializes them to the four quantifiers of `MultiFormula`.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

/-- Coercions of a truth-value family to `ℝ` are uniformly bounded above. -/
theorem bddAbove_truthValueCoeRange {ι : Type*} (values : ι → TruthValue) :
    BddAbove (Set.range fun i => (values i : ℝ)) := by
  rw [bddAbove_def]
  refine ⟨1, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact (values i).property.2

/-- Coercions of a truth-value family to `ℝ` are uniformly bounded below. -/
theorem bddBelow_truthValueCoeRange {ι : Type*} (values : ι → TruthValue) :
    BddBelow (Set.range fun i => (values i : ℝ)) := by
  rw [bddBelow_def]
  refine ⟨0, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact (values i).property.1

/-- Taking a supremum of nonempty truth-value families does not enlarge a
uniform real error. -/
theorem abs_coe_iSup_sub_coe_iSup_le {ι : Type*} [Nonempty ι]
    (first second : ι → TruthValue) {ε : ℝ}
    (h : ∀ i, |(first i : ℝ) - (second i : ℝ)| ≤ ε) :
    |(↑(⨆ i, first i) : ℝ) - (↑(⨆ i, second i) : ℝ)| ≤ ε := by
  rw [Set.Icc.coe_iSup zero_le_one, Set.Icc.coe_iSup zero_le_one,
    abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    apply ciSup_le
    intro i
    exact ((sub_le_iff_le_add.mp (abs_sub_le_iff.mp (h i)).1).trans
      (add_le_add_right
        (le_ciSup (bddAbove_truthValueCoeRange second) i) ε))
  · rw [sub_le_iff_le_add]
    apply ciSup_le
    intro i
    exact ((sub_le_iff_le_add.mp (abs_sub_le_iff.mp (h i)).2).trans
      (add_le_add_right
        (le_ciSup (bddAbove_truthValueCoeRange first) i) ε))

/-- Taking an infimum of nonempty truth-value families does not enlarge a
uniform real error. -/
theorem abs_coe_iInf_sub_coe_iInf_le {ι : Type*} [Nonempty ι]
    (first second : ι → TruthValue) {ε : ℝ}
    (h : ∀ i, |(first i : ℝ) - (second i : ℝ)| ≤ ε) :
    |(↑(⨅ i, first i) : ℝ) - (↑(⨅ i, second i) : ℝ)| ≤ ε := by
  rw [Set.Icc.coe_iInf zero_le_one, Set.Icc.coe_iInf zero_le_one,
    abs_sub_le_iff]
  constructor
  · have hlower : (⨅ i, (first i : ℝ)) - ε ≤ ⨅ i, (second i : ℝ) := by
      apply le_ciInf
      intro i
      have hle : (first i : ℝ) - ε ≤ (second i : ℝ) := by
        linarith [(abs_sub_le_iff.mp (h i)).1]
      exact (sub_le_sub_right
        (ciInf_le (bddBelow_truthValueCoeRange first) i) ε).trans hle
    exact sub_le_iff_le_add'.mpr (sub_le_iff_le_add.mp hlower)
  · have hlower : (⨅ i, (second i : ℝ)) - ε ≤ ⨅ i, (first i : ℝ) := by
      apply le_ciInf
      intro i
      have hle : (second i : ℝ) - ε ≤ (first i : ℝ) := by
        linarith [(abs_sub_le_iff.mp (h i)).2]
      exact (sub_le_sub_right
        (ciInf_le (bddBelow_truthValueCoeRange second) i) ε).trans hle
    exact sub_le_iff_le_add'.mpr (sub_le_iff_le_add.mp hlower)

namespace MultiFormula


end MultiFormula

end

end NormFormula.ContinuousLogic
