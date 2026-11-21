import NormFormula.Combinatorics.ScaleSensitiveDiscretization

/-!
# Strong shattering on a finite row set

This file isolates the combinatorial insertion step in the finite-range
scale-sensitive Sauer lemma. If two evaluation classes strongly shatter the
same thresholded row set and take values separated by two levels at a fresh
coordinate, their disjoint union strongly shatters the row set with that
coordinate inserted.
-/

namespace NormFormula

/-- A parameter class strongly shatters a specified finite set of rows at
unit integer margin around a fixed threshold function. -/
def StronglyShattersAtUnit
    {Row Parameter : Type*} [DecidableEq Row]
    (value : Row → Parameter → ℕ)
    (rows : Finset Row) (threshold : Row → ℕ) : Prop :=
  ∀ S : Finset Row, S ⊆ rows → ∃ parameter : Parameter,
    (∀ row ∈ S, threshold row + 1 ≤ value row parameter) ∧
    (∀ row ∈ rows, row ∉ S → value row parameter + 1 ≤ threshold row)

/-- Strong shattering of all rows is the earlier whole-finite-type notion. -/
theorem stronglyShattersAtUnit_univ_iff
    {Row Parameter : Type*} [Fintype Row] [DecidableEq Row]
    {value : Row → Parameter → ℕ} :
    (∃ threshold : Row → ℕ,
      StronglyShattersAtUnit value Finset.univ threshold) ↔
      IsStronglyShatteredAtUnit value := by
  constructor
  · rintro ⟨threshold, h⟩
    refine ⟨threshold, ?_⟩
    intro S
    obtain ⟨parameter, hhigh, hlow⟩ := h S (by simp)
    exact ⟨parameter, hhigh, fun row hrow ↦ hlow row (by simp) hrow⟩
  · rintro ⟨threshold, h⟩
    refine ⟨threshold, ?_⟩
    intro S hS
    obtain ⟨parameter, hhigh, hlow⟩ := h S
    exact ⟨parameter, hhigh, fun row _ hrow ↦ hlow row hrow⟩

/-- The evaluation class obtained by taking the disjoint union of two
parameter classes. -/
def sumEvaluation
    {Row LowParameter HighParameter : Type*}
    (lowValue : Row → LowParameter → ℕ)
    (highValue : Row → HighParameter → ℕ) :
    Row → LowParameter ⊕ HighParameter → ℕ :=
  fun row ↦ Sum.elim (lowValue row) (highValue row)

/-- Two fibers separated by two integer levels at a distinguished row add that row to
a common strongly shattered pair. This is the combinatorial insertion step
behind the finite-range packing recurrence. -/
theorem StronglyShattersAtUnit.insert_of_sum
    {Row LowParameter HighParameter : Type*} [DecidableEq Row]
    {lowValue : Row → LowParameter → ℕ}
    {highValue : Row → HighParameter → ℕ}
    {rows : Finset Row} {threshold : Row → ℕ}
    {newRow : Row} {lowLevel highLevel : ℕ}
    (hlowShatters : StronglyShattersAtUnit lowValue rows threshold)
    (hhighShatters : StronglyShattersAtUnit highValue rows threshold)
    (hlowLevel : ∀ parameter, lowValue newRow parameter = lowLevel)
    (hhighLevel : ∀ parameter, highValue newRow parameter = highLevel)
    (hlevels : lowLevel + 2 ≤ highLevel) :
    StronglyShattersAtUnit (sumEvaluation lowValue highValue)
      (insert newRow rows) (Function.update threshold newRow (lowLevel + 1)) := by
  intro S hS
  by_cases hnewS : newRow ∈ S
  · have heraseSubset : S.erase newRow ⊆ rows := by
      intro row hrow
      have hrowS : row ∈ S := Finset.mem_of_mem_erase hrow
      have hrowInsert := hS hrowS
      rw [Finset.mem_insert] at hrowInsert
      exact hrowInsert.resolve_left (Finset.ne_of_mem_erase hrow)
    obtain ⟨parameter, hhigh, hlow⟩ :=
      hhighShatters (S.erase newRow) heraseSubset
    refine ⟨Sum.inr parameter, ?_, ?_⟩
    · intro row hrow
      by_cases hrowNew : row = newRow
      · subst row
        simp [sumEvaluation, hhighLevel, hlevels]
      · have hrowErase : row ∈ S.erase newRow := by
          exact Finset.mem_erase.mpr ⟨hrowNew, hrow⟩
        simpa [sumEvaluation, Function.update, hrowNew] using
          hhigh row hrowErase
    · intro row hrowInsert hrowS
      have hrowNew : row ≠ newRow := by
        intro h
        subst row
        exact hrowS hnewS
      have hrowRows : row ∈ rows := by
        rw [Finset.mem_insert] at hrowInsert
        exact hrowInsert.resolve_left hrowNew
      have hrowErase : row ∉ S.erase newRow := by
        simp [hrowS]
      simpa [sumEvaluation, Function.update, hrowNew] using
        hlow row hrowRows hrowErase
  · have hsubsetRows : S ⊆ rows := by
      intro row hrow
      have hrowInsert := hS hrow
      rw [Finset.mem_insert] at hrowInsert
      exact hrowInsert.resolve_left (fun h ↦ hnewS (h ▸ hrow))
    obtain ⟨parameter, hhigh, hlow⟩ := hlowShatters S hsubsetRows
    refine ⟨Sum.inl parameter, ?_, ?_⟩
    · intro row hrow
      have hrowNew : row ≠ newRow := by
        intro h
        subst row
        exact hnewS hrow
      simpa [sumEvaluation, Function.update, hrowNew] using
        hhigh row hrow
    · intro row hrowInsert hrowS
      by_cases hrowNew : row = newRow
      · subst row
        simp [sumEvaluation, hlowLevel]
      · have hrowRows : row ∈ rows := by
          rw [Finset.mem_insert] at hrowInsert
          exact hrowInsert.resolve_left hrowNew
        simpa [sumEvaluation, Function.update, hrowNew] using
          hlow row hrowRows hrowS

/-- Strong shattering depends only on threshold values on the selected row
set. -/
theorem StronglyShattersAtUnit.congr_threshold_on_rows
    {Row Parameter : Type*} [DecidableEq Row]
    {value : Row → Parameter → ℕ} {rows : Finset Row}
    {threshold otherThreshold : Row → ℕ}
    (hshatters : StronglyShattersAtUnit value rows threshold)
    (hthreshold : ∀ row ∈ rows,
      otherThreshold row = threshold row) :
    StronglyShattersAtUnit value rows otherThreshold := by
  intro S hS
  obtain ⟨parameter, hhigh, hlow⟩ := hshatters S hS
  refine ⟨parameter, ?_, ?_⟩
  · intro row hrow
    rw [hthreshold row (hS hrow)]
    exact hhigh row hrow
  · intro row hrowRows hrowS
    rw [hthreshold row hrowRows]
    exact hlow row hrowRows hrowS

end NormFormula
