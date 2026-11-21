import NormFormula.Combinatorics.StrongPairInsertion

/-!
# The strong-pair fiber recurrence

This file packages the pairs realized by both separated coordinate fibers and
maps them injectively into new pairs realized by the parent class. Every image
pair contains the separating coordinate, so the image is disjoint from all
pairs supported on the rows with that coordinate erased.
-/

namespace NormFormula

/-- Strong pairs realized by both fixed-level fibers away from `newRow`. -/
noncomputable def commonFiberRealizedStrongPairs
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    (family : Finset (Row → ℕ)) (activeRows : Finset Row)
    (levelCount : ℕ) (newRow : Row) (lowLevel highLevel : ℕ) :
    Finset (BoundedThresholdPair Row levelCount (Fintype.card Row)) := by
  classical
  exact (realizedStrongPairsOn (coordinateFiber family newRow lowLevel)
      (activeRows.erase newRow) levelCount (Fintype.card Row) ∩
    realizedStrongPairsOn (coordinateFiber family newRow highLevel)
      (activeRows.erase newRow) levelCount (Fintype.card Row))

/-- Insert the separating coordinate into a pair common to both fibers. -/
def insertCommonFiberRealizedStrongPair
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {family : Finset (Row → ℕ)} {activeRows : Finset Row}
    {levelCount : ℕ} {newRow : Row} {lowLevel highLevel : ℕ}
    (hhighBound : highLevel < levelCount)
    (hlevels : lowLevel + 2 ≤ highLevel)
    (pair : ↥(commonFiberRealizedStrongPairs family activeRows levelCount
      newRow lowLevel highLevel)) :
    BoundedThresholdPair Row levelCount (Fintype.card Row) := by
  classical
  have hlow := (Finset.mem_inter.mp pair.2).1
  let insertable := insertableThresholdPairOfSubsetErase pair.1
    (mem_realizedStrongPairsOn.mp hlow).2.1
  let newThreshold : Fin levelCount := ⟨lowLevel + 1, by omega⟩
  exact insertBoundedThresholdPair newThreshold insertable

/-- The common-pair insertion map is injective. -/
theorem insertCommonFiberRealizedStrongPair_injective
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {family : Finset (Row → ℕ)} {activeRows : Finset Row}
    {levelCount : ℕ} {newRow : Row} {lowLevel highLevel : ℕ}
    (hhighBound : highLevel < levelCount)
    (hlevels : lowLevel + 2 ≤ highLevel) :
    Function.Injective
      (insertCommonFiberRealizedStrongPair
        (family := family) (activeRows := activeRows)
        (newRow := newRow)
        hhighBound hlevels) := by
  classical
  intro p q hpq
  apply Subtype.ext
  let newThreshold : Fin levelCount := ⟨lowLevel + 1, by omega⟩
  change insertBoundedThresholdPair newThreshold _ =
    insertBoundedThresholdPair newThreshold _ at hpq
  have hinsertable := insertBoundedThresholdPair_injective newThreshold hpq
  exact congrArg
    (fun pair : InsertableThresholdPair Row levelCount
      (Fintype.card Row) newRow ↦ pair.1) hinsertable

/-- Every inserted common-fiber pair is realized by the parent class. -/
theorem insertCommonFiberRealizedStrongPair_mem_parent
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {family : Finset (Row → ℕ)} {activeRows : Finset Row}
    {levelCount : ℕ} {newRow : Row} {lowLevel highLevel : ℕ}
    (hnewActive : newRow ∈ activeRows)
    (hhighBound : highLevel < levelCount)
    (hlevels : lowLevel + 2 ≤ highLevel)
    (pair : ↥(commonFiberRealizedStrongPairs family activeRows levelCount
      newRow lowLevel highLevel)) :
    insertCommonFiberRealizedStrongPair hhighBound hlevels pair ∈
      realizedStrongPairsOn family activeRows levelCount
        (Fintype.card Row) := by
  classical
  have hlow := (Finset.mem_inter.mp pair.2).1
  have hhigh := (Finset.mem_inter.mp pair.2).2
  exact insertBoundedThresholdPair_mem_realized_of_mem_both_fibers
    hnewActive hhighBound hlevels pair.1 hlow hhigh

/-- Every inserted common pair contains the separating coordinate. -/
theorem newRow_mem_insertCommonFiberRealizedStrongPair_rows
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {family : Finset (Row → ℕ)} {activeRows : Finset Row}
    {levelCount : ℕ} {newRow : Row} {lowLevel highLevel : ℕ}
    (hhighBound : highLevel < levelCount)
    (hlevels : lowLevel + 2 ≤ highLevel)
    (pair : ↥(commonFiberRealizedStrongPairs family activeRows levelCount
      newRow lowLevel highLevel)) :
    newRow ∈ (insertCommonFiberRealizedStrongPair
      hhighBound hlevels pair).rows := by
  classical
  rw [insertCommonFiberRealizedStrongPair,
    insertBoundedThresholdPair_rows]
  exact Finset.mem_insert_self _ _

/-- Hence an inserted common pair is not supported entirely away from the
separating coordinate. -/
theorem insertCommonFiberRealizedStrongPair_not_mem_away
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {family : Finset (Row → ℕ)} {activeRows : Finset Row}
    {levelCount : ℕ} {newRow : Row} {lowLevel highLevel : ℕ}
    (hhighBound : highLevel < levelCount)
    (hlevels : lowLevel + 2 ≤ highLevel)
    (pair : ↥(commonFiberRealizedStrongPairs family activeRows levelCount
      newRow lowLevel highLevel)) :
    insertCommonFiberRealizedStrongPair hhighBound hlevels pair ∉
      realizedStrongPairsOn family (activeRows.erase newRow) levelCount
        (Fintype.card Row) := by
  classical
  intro haway
  have hsupport := (mem_realizedStrongPairsOn.mp haway).2.1
  have hnew := hsupport
    (newRow_mem_insertCommonFiberRealizedStrongPair_rows
      hhighBound hlevels pair)
  exact (Finset.mem_erase.mp hnew).1 rfl

/-- The finite image of the common-fiber pair insertion map. -/
noncomputable def insertedCommonFiberRealizedStrongPairs
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    (family : Finset (Row → ℕ)) (activeRows : Finset Row)
    (levelCount : ℕ) (newRow : Row) (lowLevel highLevel : ℕ)
    (hhighBound : highLevel < levelCount)
    (hlevels : lowLevel + 2 ≤ highLevel) :
    Finset (BoundedThresholdPair Row levelCount (Fintype.card Row)) := by
  classical
  exact (commonFiberRealizedStrongPairs family activeRows levelCount
    newRow lowLevel highLevel).attach.image
      (insertCommonFiberRealizedStrongPair hhighBound hlevels)

/-- The inserted image has exactly the cardinality of the common-pair
intersection. -/
theorem card_insertedCommonFiberRealizedStrongPairs
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    (family : Finset (Row → ℕ)) (activeRows : Finset Row)
    (levelCount : ℕ) (newRow : Row) (lowLevel highLevel : ℕ)
    (hhighBound : highLevel < levelCount)
    (hlevels : lowLevel + 2 ≤ highLevel) :
    (insertedCommonFiberRealizedStrongPairs family activeRows levelCount
      newRow lowLevel highLevel hhighBound hlevels).card =
      (commonFiberRealizedStrongPairs family activeRows levelCount
        newRow lowLevel highLevel).card := by
  classical
  unfold insertedCommonFiberRealizedStrongPairs
  rw [Finset.card_image_of_injective]
  · exact Finset.card_attach
  · exact insertCommonFiberRealizedStrongPair_injective
      hhighBound hlevels

/-- The inserted image is contained in the parent realized-pair set. -/
theorem insertedCommonFiberRealizedStrongPairs_subset_parent
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {family : Finset (Row → ℕ)} {activeRows : Finset Row}
    {levelCount : ℕ} {newRow : Row} {lowLevel highLevel : ℕ}
    (hnewActive : newRow ∈ activeRows)
    (hhighBound : highLevel < levelCount)
    (hlevels : lowLevel + 2 ≤ highLevel) :
    insertedCommonFiberRealizedStrongPairs family activeRows levelCount
        newRow lowLevel highLevel hhighBound hlevels ⊆
      realizedStrongPairsOn family activeRows levelCount
        (Fintype.card Row) := by
  classical
  intro pair hpair
  rw [insertedCommonFiberRealizedStrongPairs,
    Finset.mem_image] at hpair
  obtain ⟨commonPair, _, rfl⟩ := hpair
  exact insertCommonFiberRealizedStrongPair_mem_parent
    hnewActive hhighBound hlevels commonPair

/-- The inserted image is disjoint from every pair supported away from the
separating coordinate. -/
theorem insertedCommonFiberRealizedStrongPairs_disjoint_away
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {family : Finset (Row → ℕ)} {activeRows : Finset Row}
    {levelCount : ℕ} {newRow : Row} {lowLevel highLevel : ℕ}
    (hhighBound : highLevel < levelCount)
    (hlevels : lowLevel + 2 ≤ highLevel) :
    Disjoint
      (insertedCommonFiberRealizedStrongPairs family activeRows levelCount
        newRow lowLevel highLevel hhighBound hlevels)
      (realizedStrongPairsOn family (activeRows.erase newRow) levelCount
        (Fintype.card Row)) := by
  classical
  rw [Finset.disjoint_left]
  intro pair hinserted haway
  rw [insertedCommonFiberRealizedStrongPairs,
    Finset.mem_image] at hinserted
  obtain ⟨commonPair, _, rfl⟩ := hinserted
  exact insertCommonFiberRealizedStrongPair_not_mem_away
    hhighBound hlevels commonPair haway

/-- Cardinal form of the strong-pair fiber recurrence: the parent class
realizes at least the sum of the numbers of pairs realized by the two
separated fibers. -/
theorem add_card_fiber_realizedStrongPairsOn_le_parent
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {family : Finset (Row → ℕ)} {activeRows : Finset Row}
    {levelCount : ℕ} {newRow : Row} {lowLevel highLevel : ℕ}
    (hnewActive : newRow ∈ activeRows)
    (hhighBound : highLevel < levelCount)
    (hlevels : lowLevel + 2 ≤ highLevel) :
    (realizedStrongPairsOn (coordinateFiber family newRow lowLevel)
        (activeRows.erase newRow) levelCount (Fintype.card Row)).card +
      (realizedStrongPairsOn (coordinateFiber family newRow highLevel)
        (activeRows.erase newRow) levelCount (Fintype.card Row)).card ≤
      (realizedStrongPairsOn family activeRows levelCount
        (Fintype.card Row)).card := by
  classical
  let lowPairs := realizedStrongPairsOn
    (coordinateFiber family newRow lowLevel) (activeRows.erase newRow)
      levelCount (Fintype.card Row)
  let highPairs := realizedStrongPairsOn
    (coordinateFiber family newRow highLevel) (activeRows.erase newRow)
      levelCount (Fintype.card Row)
  let awayPairs := realizedStrongPairsOn family (activeRows.erase newRow)
    levelCount (Fintype.card Row)
  let parentPairs := realizedStrongPairsOn family activeRows
    levelCount (Fintype.card Row)
  let insertedPairs := insertedCommonFiberRealizedStrongPairs
    family activeRows levelCount newRow lowLevel highLevel hhighBound hlevels
  have hlowAway : lowPairs ⊆ awayPairs := by
    exact realizedStrongPairsOn_coordinateFiber_subset
      family (activeRows.erase newRow) newRow lowLevel
        levelCount (Fintype.card Row)
  have hhighAway : highPairs ⊆ awayPairs := by
    exact realizedStrongPairsOn_coordinateFiber_subset
      family (activeRows.erase newRow) newRow highLevel
        levelCount (Fintype.card Row)
  have hawayParent : awayPairs ⊆ parentPairs := by
    apply realizedStrongPairsOn_mono_rows
    exact Finset.erase_subset newRow activeRows
  have hunionParent : lowPairs ∪ highPairs ⊆ parentPairs := by
    intro pair hpair
    rw [Finset.mem_union] at hpair
    exact hpair.elim
      (fun hp ↦ hawayParent (hlowAway hp))
      (fun hp ↦ hawayParent (hhighAway hp))
  have hinsertedParent : insertedPairs ⊆ parentPairs := by
    exact insertedCommonFiberRealizedStrongPairs_subset_parent
      hnewActive hhighBound hlevels
  have hunionAway : lowPairs ∪ highPairs ⊆ awayPairs := by
    intro pair hpair
    rw [Finset.mem_union] at hpair
    exact hpair.elim
      (fun hp ↦ hlowAway hp)
      (fun hp ↦ hhighAway hp)
  have hdisjoint : Disjoint insertedPairs (lowPairs ∪ highPairs) := by
    exact (insertedCommonFiberRealizedStrongPairs_disjoint_away
      (family := family) (activeRows := activeRows)
      hhighBound hlevels).mono_right hunionAway
  have hcombinedSubset : (lowPairs ∪ highPairs) ∪ insertedPairs ⊆
      parentPairs := by
    intro pair hpair
    rw [Finset.mem_union] at hpair
    exact hpair.elim
      (fun hp ↦ hunionParent hp)
      (fun hp ↦ hinsertedParent hp)
  have hinsertedCard : insertedPairs.card = (lowPairs ∩ highPairs).card := by
    exact card_insertedCommonFiberRealizedStrongPairs
      family activeRows levelCount newRow lowLevel highLevel
        hhighBound hlevels
  calc
    lowPairs.card + highPairs.card =
        (lowPairs ∪ highPairs).card + (lowPairs ∩ highPairs).card :=
      (Finset.card_union_add_card_inter lowPairs highPairs).symm
    _ = (lowPairs ∪ highPairs).card + insertedPairs.card := by
      rw [hinsertedCard]
    _ = ((lowPairs ∪ highPairs) ∪ insertedPairs).card := by
      rw [Finset.card_union_of_disjoint hdisjoint.symm]
    _ ≤ parentPairs.card := Finset.card_le_card hcombinedSubset

end NormFormula
