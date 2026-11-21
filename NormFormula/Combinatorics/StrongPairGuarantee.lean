import NormFormula.Combinatorics.StrongPairRecurrence

/-!
# Uniform lower guarantees for realized strong pairs

This file packages the finite fiber recurrence in the uniform form used for
iteration: every sufficiently large bounded-range, pairwise two-separated
class on a fixed active row set realizes a prescribed number of nonempty
strong-threshold pairs.
-/

namespace NormFormula

/-- A uniform lower bound on the number of strong pairs realized by every
sufficiently large bounded-range, pairwise two-separated finite class. -/
def GuaranteesRealizedStrongPairCount
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    (activeRows : Finset Row) (levelCount minimumFamilySize pairCount : ℕ) :
    Prop :=
  ∀ family : Finset (Row → ℕ),
    minimumFamilySize ≤ family.card →
    IsPairwiseTwoSeparatedOn family activeRows →
    (∀ f ∈ family, ∀ row ∈ activeRows, f row < levelCount) →
    pairCount ≤ (realizedStrongPairsOn family activeRows levelCount
      (Fintype.card Row)).card

/-- Uniform fiber recurrence. The factor `2` forms disjoint pairs, and
`activeRows.card * levelCount^2` is the number of ordered separation codes.
Two extracted fibers each realize `pairCount` pairs; the strong-pair cardinal
recurrence adds their contributions. -/
theorem guaranteesRealizedStrongPairCount_step
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {activeRows : Finset Row} {levelCount childFamilySize pairCount : ℕ}
    (hactive : activeRows.Nonempty)
    (hlevelCount : 0 < levelCount)
    (hchildSize : 0 < childFamilySize)
    (hchild : ∀ row ∈ activeRows,
      GuaranteesRealizedStrongPairCount (activeRows.erase row)
        levelCount childFamilySize pairCount) :
    GuaranteesRealizedStrongPairCount activeRows levelCount
      (2 * ((activeRows.card * levelCount * levelCount) * childFamilySize))
      (2 * pairCount) := by
  intro family hfamily hseparated hbounded
  obtain ⟨row, hrow, lowLevel, highLevel, _, hhighBound, hlevels,
    hlowCard, hhighCard⟩ :=
    exists_large_separated_coordinateFibers_of_card
      hactive hlevelCount hchildSize hseparated hbounded hfamily
  have hlowPairs : pairCount ≤
      (realizedStrongPairsOn (coordinateFiber family row lowLevel)
        (activeRows.erase row) levelCount (Fintype.card Row)).card := by
    apply hchild row hrow (coordinateFiber family row lowLevel)
      hlowCard (hseparated.coordinateFiber_erase row lowLevel)
    intro f hf activeRow hactiveRow
    exact hbounded f (mem_coordinateFiber.mp hf).1 activeRow
      (Finset.mem_erase.mp hactiveRow).2
  have hhighPairs : pairCount ≤
      (realizedStrongPairsOn (coordinateFiber family row highLevel)
        (activeRows.erase row) levelCount (Fintype.card Row)).card := by
    apply hchild row hrow (coordinateFiber family row highLevel)
      hhighCard (hseparated.coordinateFiber_erase row highLevel)
    intro f hf activeRow hactiveRow
    exact hbounded f (mem_coordinateFiber.mp hf).1 activeRow
      (Finset.mem_erase.mp hactiveRow).2
  have hparent := add_card_fiber_realizedStrongPairsOn_le_parent
    (family := family) hrow hhighBound hlevels
  omega

/-- Two functions separated at one active row strongly shatter the singleton
pair at that row. -/
theorem realizedStrongPairsOn_nonempty_of_two_level_witness
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {family : Finset (Row → ℕ)} {activeRows : Finset Row}
    {levelCount : ℕ} {low high : Row → ℕ} {row : Row}
    (hlowMem : low ∈ family) (hhighMem : high ∈ family)
    (hrow : row ∈ activeRows)
    (hgap : low row + 2 ≤ high row)
    (hhighBound : high row < levelCount) :
    (realizedStrongPairsOn family activeRows levelCount
      (Fintype.card Row)).Nonempty := by
  classical
  have hcardRow : 0 < Fintype.card Row := Fintype.card_pos_iff.mpr ⟨row⟩
  let pairSize : Fin (Fintype.card Row + 1) :=
    ⟨1, Nat.succ_lt_succ hcardRow⟩
  let pairRows :
      ↥((Finset.univ : Finset Row).powersetCard pairSize) :=
    ⟨{row}, by simp [pairSize]⟩
  let pairThreshold : ↥(pairRows : Finset Row) → Fin levelCount :=
    fun _ ↦ ⟨low row + 1, by omega⟩
  let pair : BoundedThresholdPair Row levelCount (Fintype.card Row) :=
    ⟨pairSize, pairRows, pairThreshold⟩
  have hsingleton : StronglyShattersAtUnit
      (finiteClassEvaluation family) {row} (fun _ ↦ low row + 1) := by
    intro S hS
    by_cases hrowS : row ∈ S
    · refine ⟨⟨high, hhighMem⟩, ?_, ?_⟩
      · intro activeRow hactiveRow
        have hactiveEq : activeRow = row := by
          exact Finset.mem_singleton.mp (hS hactiveRow)
        subst activeRow
        change low row + 1 + 1 ≤ high row
        omega
      · intro activeRow hactiveSingleton hactiveNot
        have hactiveEq : activeRow = row :=
          Finset.mem_singleton.mp hactiveSingleton
        subst activeRow
        exact (hactiveNot hrowS).elim
    · refine ⟨⟨low, hlowMem⟩, ?_, ?_⟩
      · intro activeRow hactiveRow
        have hactiveEq : activeRow = row := by
          exact Finset.mem_singleton.mp (hS hactiveRow)
        subst activeRow
        exact (hrowS hactiveRow).elim
      · intro activeRow hactiveSingleton _
        have hactiveEq : activeRow = row :=
          Finset.mem_singleton.mp hactiveSingleton
        subst activeRow
        rfl
  refine ⟨pair, ?_⟩
  rw [mem_realizedStrongPairsOn]
  refine ⟨?_, ?_, ?_⟩
  · change ({row} : Finset Row).Nonempty
    exact Finset.singleton_nonempty row
  · change ({row} : Finset Row) ⊆ activeRows
    simpa using hrow
  · apply hsingleton.congr_threshold_on_rows
    intro activeRow hactiveRow
    have hactiveEq : activeRow = row :=
      Finset.mem_singleton.mp hactiveRow
    subst activeRow
    have hrowPair : row ∈ pair.rows := by
      change row ∈ ({row} : Finset Row)
      simp
    rw [BoundedThresholdPair.threshold_apply_of_mem pair hrowPair]

/-- Base of the strong-pair recurrence: every pairwise two-separated class of
at least two functions realizes at least one nonempty strong pair. -/
theorem guaranteesRealizedStrongPairCount_two_one
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    (activeRows : Finset Row) (levelCount : ℕ) :
    GuaranteesRealizedStrongPairCount activeRows levelCount 2 1 := by
  intro family hfamily hseparated hbounded
  have hone : 1 < family.card := lt_of_lt_of_le (by omega) hfamily
  obtain ⟨f, hf, g, hg, hfg⟩ := Finset.one_lt_card.mp hone
  obtain ⟨row, hrow, hgap⟩ := hseparated f hf g hg hfg
  rcases hgap with hgap | hgap
  · have hnonempty := realizedStrongPairsOn_nonempty_of_two_level_witness
      hf hg hrow hgap (hbounded g hg row hrow)
    exact Finset.card_pos.mpr hnonempty
  · have hnonempty := realizedStrongPairsOn_nonempty_of_two_level_witness
      hg hf hrow hgap (hbounded f hf row hrow)
    exact Finset.card_pos.mpr hnonempty

end NormFormula
