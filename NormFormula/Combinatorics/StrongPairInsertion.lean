import NormFormula.Combinatorics.RealizedStrongPairs

/-!
# Canonical insertion of a strong-threshold coordinate

Threshold assignments are stored dependently only on their selected rows.
This file proves an extensionality principle for that representation and
constructs the canonical, injective operation which inserts one fresh row and
one threshold level into a bounded pair.
-/

namespace NormFormula

/-- A bounded threshold pair is determined by its row set and its
zero-extended threshold function. -/
theorem BoundedThresholdPair.ext_rows_threshold
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {levelCount dimension : ℕ}
    {p q : BoundedThresholdPair Row levelCount dimension}
    (hrows : p.rows = q.rows)
    (hthreshold : p.threshold = q.threshold) : p = q := by
  rcases p with ⟨pk, prows, pthreshold⟩
  rcases q with ⟨qk, qrows, qthreshold⟩
  dsimp [BoundedThresholdPair.rows] at hrows
  have hk : pk = qk := by
    apply Fin.ext
    have hp := (Finset.mem_powersetCard.mp prows.property).2
    have hq := (Finset.mem_powersetCard.mp qrows.property).2
    rw [← hp, ← hq]
    exact congrArg Finset.card hrows
  subst qk
  have hrowSubtype : prows = qrows := by
    apply Subtype.ext
    exact hrows
  subst qrows
  congr 2
  funext row
  apply Fin.ext
  have hmem : row.1 ∈ (prows : Finset Row) := row.2
  have happly := congrFun hthreshold row.1
  simpa [BoundedThresholdPair.threshold, hmem] using happly

/-- Pairs into which `newRow` can be inserted without exceeding the fixed
dimension index. -/
def InsertableThresholdPair
    (Row : Type*) [Fintype Row] [DecidableEq Row]
    (levelCount dimension : ℕ) (newRow : Row) :=
  {pair : BoundedThresholdPair Row levelCount dimension //
    newRow ∉ pair.rows ∧ pair.rows.card < dimension}

/-- Insert one fresh row with a prescribed finite-range threshold. -/
def insertBoundedThresholdPair
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {levelCount dimension : ℕ} {newRow : Row}
    (newThreshold : Fin levelCount)
    (pair : InsertableThresholdPair Row levelCount dimension newRow) :
    BoundedThresholdPair Row levelCount dimension := by
  let newSize : Fin (dimension + 1) := ⟨pair.1.1 + 1, by
    rw [Nat.lt_succ_iff]
    have hp : pair.1.1 < dimension := by
      simpa [pair.1.card_rows] using pair.2.2
    omega⟩
  let newRows :
      ↥((Finset.univ : Finset Row).powersetCard newSize) :=
    ⟨insert newRow pair.1.rows, by
      rw [Finset.mem_powersetCard]
      constructor
      · exact Finset.subset_univ _
      · rw [Finset.card_insert_of_notMem pair.2.1, pair.1.card_rows]⟩
  let newThresholds : ↥(newRows : Finset Row) → Fin levelCount :=
    fun row ↦ if hrow : row.1 = newRow then newThreshold else
      pair.1.2.2 ⟨row.1, by
        have hmem := row.2
        change row.1 ∈ insert newRow pair.1.rows at hmem
        exact (Finset.mem_insert.mp hmem).resolve_left hrow⟩
  exact ⟨newSize, newRows, newThresholds⟩

@[simp] theorem insertBoundedThresholdPair_rows
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {levelCount dimension : ℕ} {newRow : Row}
    (newThreshold : Fin levelCount)
    (pair : InsertableThresholdPair Row levelCount dimension newRow) :
    (insertBoundedThresholdPair newThreshold pair).rows =
      insert newRow pair.1.rows := by
  rfl

@[simp] theorem insertBoundedThresholdPair_threshold_new
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {levelCount dimension : ℕ} {newRow : Row}
    (newThreshold : Fin levelCount)
    (pair : InsertableThresholdPair Row levelCount dimension newRow) :
    (insertBoundedThresholdPair newThreshold pair).threshold newRow =
      newThreshold := by
  rw [BoundedThresholdPair.threshold_apply_of_mem]
  · simp [insertBoundedThresholdPair]
  · change newRow ∈ insert newRow pair.1.rows
    simp

@[simp] theorem insertBoundedThresholdPair_threshold_of_mem
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {levelCount dimension : ℕ} {newRow : Row}
    (newThreshold : Fin levelCount)
    (pair : InsertableThresholdPair Row levelCount dimension newRow)
    {row : Row} (hrow : row ∈ pair.1.rows) :
    (insertBoundedThresholdPair newThreshold pair).threshold row =
      pair.1.threshold row := by
  have hne : row ≠ newRow := fun h ↦ pair.2.1 (h ▸ hrow)
  rw [BoundedThresholdPair.threshold_apply_of_mem]
  · simp [insertBoundedThresholdPair, hrow, hne,
      BoundedThresholdPair.threshold]
  · change row ∈ insert newRow pair.1.rows
    simp [hrow]

/-- Insertion at a fixed row and threshold level is injective. -/
theorem insertBoundedThresholdPair_injective
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {levelCount dimension : ℕ} {newRow : Row}
    (newThreshold : Fin levelCount) :
    Function.Injective
      (insertBoundedThresholdPair (newRow := newRow) newThreshold :
        InsertableThresholdPair Row levelCount dimension newRow →
          BoundedThresholdPair Row levelCount dimension) := by
  intro p q hpq
  apply Subtype.ext
  apply BoundedThresholdPair.ext_rows_threshold
  · have hrows := congrArg BoundedThresholdPair.rows hpq
    rw [insertBoundedThresholdPair_rows,
      insertBoundedThresholdPair_rows] at hrows
    have herase := congrArg (fun rows : Finset Row ↦ rows.erase newRow) hrows
    simpa [p.2.1, q.2.1] using herase
  · funext row
    have hrows := congrArg BoundedThresholdPair.rows hpq
    rw [insertBoundedThresholdPair_rows,
      insertBoundedThresholdPair_rows] at hrows
    have horiginalRows : p.1.rows = q.1.rows := by
      have herase := congrArg
        (fun rows : Finset Row ↦ rows.erase newRow) hrows
      simpa [p.2.1, q.2.1] using herase
    by_cases hrow : row ∈ p.1.rows
    · have hrowQ : row ∈ q.1.rows := by
        simpa [horiginalRows] using hrow
      have hthresholds := congrArg BoundedThresholdPair.threshold hpq
      calc
        p.1.threshold row =
            (insertBoundedThresholdPair newThreshold p).threshold row :=
          (insertBoundedThresholdPair_threshold_of_mem
            newThreshold p hrow).symm
        _ = (insertBoundedThresholdPair newThreshold q).threshold row :=
          congrFun hthresholds row
        _ = q.1.threshold row :=
          insertBoundedThresholdPair_threshold_of_mem
            newThreshold q hrowQ
    · have hrowQ : row ∉ q.1.rows := by
        simpa [horiginalRows] using hrow
      simp [BoundedThresholdPair.threshold, hrow, hrowQ]

/-- A pair supported away from `newRow` is insertable when the dimension
index is the cardinality of the whole finite row type. -/
def insertableThresholdPairOfSubsetErase
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {levelCount : ℕ} {newRow : Row} {activeRows : Finset Row}
    (pair : BoundedThresholdPair Row levelCount (Fintype.card Row))
    (hsubset : pair.rows ⊆ activeRows.erase newRow) :
    InsertableThresholdPair Row levelCount (Fintype.card Row) newRow := by
  have hnew : newRow ∉ pair.rows := by
    intro hmem
    exact (Finset.mem_erase.mp (hsubset hmem)).1 rfl
  refine ⟨pair, hnew, ?_⟩
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨Finset.subset_univ _, ?_⟩
  intro heq
  apply hnew
  rw [heq]
  exact Finset.mem_univ newRow

/-- Inserting the separating coordinate sends every strong pair realized by
both fixed-level fibers to a strong pair realized by the parent class. -/
theorem insertBoundedThresholdPair_mem_realized_of_mem_both_fibers
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {family : Finset (Row → ℕ)} {activeRows : Finset Row}
    {levelCount : ℕ} {newRow : Row} {lowLevel highLevel : ℕ}
    (hnewActive : newRow ∈ activeRows)
    (hhighBound : highLevel < levelCount)
    (hlevels : lowLevel + 2 ≤ highLevel)
    (pair : BoundedThresholdPair Row levelCount (Fintype.card Row))
    (hlow : pair ∈ realizedStrongPairsOn
      (coordinateFiber family newRow lowLevel) (activeRows.erase newRow)
      levelCount (Fintype.card Row))
    (hhigh : pair ∈ realizedStrongPairsOn
      (coordinateFiber family newRow highLevel) (activeRows.erase newRow)
      levelCount (Fintype.card Row)) :
    let insertable := insertableThresholdPairOfSubsetErase pair
      (mem_realizedStrongPairsOn.mp hlow).2.1
    let newThreshold : Fin levelCount := ⟨lowLevel + 1, by omega⟩
    insertBoundedThresholdPair newThreshold insertable ∈
      realizedStrongPairsOn family activeRows levelCount
        (Fintype.card Row) := by
  dsimp only
  let insertable := insertableThresholdPairOfSubsetErase pair
    (mem_realizedStrongPairsOn.mp hlow).2.1
  let newThreshold : Fin levelCount := ⟨lowLevel + 1, by omega⟩
  rw [mem_realizedStrongPairsOn]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨newRow, ?_⟩
    rw [insertBoundedThresholdPair_rows]
    exact Finset.mem_insert_self newRow pair.rows
  · intro row hrow
    rw [insertBoundedThresholdPair_rows] at hrow
    rcases Finset.mem_insert.mp hrow with hrowNew | hrowOld
    · simpa [hrowNew] using hnewActive
    · have hrowErase := (mem_realizedStrongPairsOn.mp hlow).2.1 hrowOld
      exact (Finset.mem_erase.mp hrowErase).2
  · have hlowShatters := (mem_realizedStrongPairsOn.mp hlow).2.2
    have hhighShatters := (mem_realizedStrongPairsOn.mp hhigh).2.2
    have hcombined := StronglyShattersAtUnit.insert_of_coordinateFibers
      hlowShatters hhighShatters hlevels
    apply hcombined.congr_threshold_on_rows
    intro row hrow
    rcases Finset.mem_insert.mp hrow with hrowNew | hrowOld
    · subst row
      calc
        (insertBoundedThresholdPair newThreshold insertable).threshold
            newRow = (newThreshold : ℕ) :=
          insertBoundedThresholdPair_threshold_new newThreshold insertable
        _ = Function.update pair.threshold newRow (lowLevel + 1)
            newRow := by simp [newThreshold, Function.update]
    · have hrowNe : row ≠ newRow := by
        intro heq
        subst row
        exact insertable.2.1 hrowOld
      have hrowInsertable : row ∈ insertable.1.rows := by
        change row ∈ pair.rows
        exact hrowOld
      calc
        (insertBoundedThresholdPair newThreshold insertable).threshold row =
            insertable.1.threshold row :=
          insertBoundedThresholdPair_threshold_of_mem
            newThreshold insertable hrowInsertable
        _ = pair.threshold row := rfl
        _ = Function.update pair.threshold newRow (lowLevel + 1) row := by
          simp [Function.update, hrowNe]

end NormFormula
