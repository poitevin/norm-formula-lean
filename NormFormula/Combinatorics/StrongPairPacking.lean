import NormFormula.Combinatorics.StrongPairDimension

/-!
# Finite-range packing from bounded strong-shattering dimension

This file combines the iterated strong-pair lower bound with the exact count
of dimension-bounded threshold pairs. The final contrapositive is the finite-
range packing theorem used after scale-sensitive discretization.
-/

namespace NormFormula

/-- A finite natural-valued function class strongly shatters no active-row
support of cardinality greater than `dimension`. -/
def HasStrongShatteringDimensionAtMostOn
    {Row : Type*} [DecidableEq Row]
    (family : Finset (Row → ℕ)) (activeRows : Finset Row)
    (dimension : ℕ) : Prop :=
  ∀ rows : Finset Row, rows ⊆ activeRows → ∀ threshold : Row → ℕ,
    StronglyShattersAtUnit (finiteClassEvaluation family) rows threshold →
      rows.card ≤ dimension

/-- A strong-dimension bound supplies the support-size hypothesis needed by
the dependent dimension-reindexing count. -/
theorem card_realizedStrongPairsOn_le_of_strongDimension
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    (family : Finset (Row → ℕ)) (activeRows : Finset Row)
    (levelCount dimension : ℕ)
    (hdimension : HasStrongShatteringDimensionAtMostOn
      family activeRows dimension) :
    (realizedStrongPairsOn family activeRows levelCount
        (Fintype.card Row)).card ≤
      strongShatteringPairBound (Fintype.card Row) levelCount dimension := by
  apply card_realizedStrongPairsOn_le_of_card_rows_le
  intro pair hpair
  rw [mem_realizedStrongPairsOn] at hpair
  exact hdimension pair.rows hpair.2.1 pair.threshold hpair.2.2

/-- Lower-versus-upper comparison: a separated class meeting the iterated
size threshold forces `2^steps` to fit inside the exact dimension-bounded
threshold-pair count. -/
theorem two_pow_le_strongShatteringPairBound_of_card
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {family : Finset (Row → ℕ)} {activeRows : Finset Row}
    {levelCount dimension steps : ℕ}
    (hlevelCount : 0 < levelCount) (hsteps : steps ≤ activeRows.card)
    (hfamily : strongPairIterationFamilySize activeRows.card levelCount steps ≤
      family.card)
    (hseparated : IsPairwiseTwoSeparatedOn family activeRows)
    (hbounded : ∀ f ∈ family, ∀ row ∈ activeRows,
      f row < levelCount)
    (hdimension : HasStrongShatteringDimensionAtMostOn
      family activeRows dimension) :
    2 ^ steps ≤
      strongShatteringPairBound (Fintype.card Row) levelCount dimension := by
  have hlower := guaranteesRealizedStrongPairCount_iteration
    activeRows levelCount steps hlevelCount hsteps
    family hfamily hseparated hbounded
  exact hlower.trans
    (card_realizedStrongPairsOn_le_of_strongDimension
      family activeRows levelCount dimension hdimension)

/-- Finite-range packing theorem. If `steps` is chosen so that `2^steps`
exceeds the total number of dimension-bounded threshold pairs, then every
bounded, pairwise two-separated class has size below the iterated recurrence
threshold. -/
theorem card_lt_strongPairIterationFamilySize
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {family : Finset (Row → ℕ)} {activeRows : Finset Row}
    {levelCount dimension steps : ℕ}
    (hlevelCount : 0 < levelCount) (hsteps : steps ≤ activeRows.card)
    (hcount : strongShatteringPairBound (Fintype.card Row)
      levelCount dimension < 2 ^ steps)
    (hseparated : IsPairwiseTwoSeparatedOn family activeRows)
    (hbounded : ∀ f ∈ family, ∀ row ∈ activeRows,
      f row < levelCount)
    (hdimension : HasStrongShatteringDimensionAtMostOn
      family activeRows dimension) :
    family.card <
      strongPairIterationFamilySize activeRows.card levelCount steps := by
  by_contra hnot
  have hfamily : strongPairIterationFamilySize activeRows.card
      levelCount steps ≤ family.card := Nat.le_of_not_gt hnot
  have hcomparison := two_pow_le_strongShatteringPairBound_of_card
    hlevelCount hsteps hfamily hseparated hbounded hdimension
  omega

end NormFormula
