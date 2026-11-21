import NormFormula.Combinatorics.FinitePairingPigeonhole

/-!
# Strong-threshold pairs realized by a finite class

This file turns the strong pairs realized by a finite natural-valued function
class into an actual finite set. It records the ambient counting bound and the
monotonicity facts needed by the fiber recurrence.
-/

namespace NormFormula

/-- Inclusion of one finite function class into a larger one. -/
def finiteClassInclusion
    {Row : Type*} {small large : Finset (Row → ℕ)}
    (hsubset : small ⊆ large) : ↥small → ↥large :=
  fun f ↦ ⟨f.1, hsubset f.2⟩

/-- Strong shattering by a finite class is monotone under enlarging the
class. -/
theorem StronglyShattersAtUnit.mono_finiteClass
    {Row : Type*} [DecidableEq Row]
    {small large : Finset (Row → ℕ)}
    {rows : Finset Row} {threshold : Row → ℕ}
    (hshatters : StronglyShattersAtUnit
      (finiteClassEvaluation small) rows threshold)
    (hsubset : small ⊆ large) :
    StronglyShattersAtUnit
      (finiteClassEvaluation large) rows threshold := by
  apply hshatters.reparam (finiteClassInclusion hsubset)
  intro row parameter
  rfl

/-- The nonempty bounded threshold pairs, supported on `activeRows`, which are
strongly shattered by a finite function class. -/
noncomputable def realizedStrongPairsOn
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    (family : Finset (Row → ℕ)) (activeRows : Finset Row)
    (levelCount dimension : ℕ) :
    Finset (BoundedThresholdPair Row levelCount dimension) := by
  classical
  exact Finset.univ.filter fun pair ↦
    pair.rows.Nonempty ∧ pair.rows ⊆ activeRows ∧
      pair.IsStronglyShatteredBy (finiteClassEvaluation family)

@[simp] theorem mem_realizedStrongPairsOn
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {family : Finset (Row → ℕ)} {activeRows : Finset Row}
    {levelCount dimension : ℕ}
    {pair : BoundedThresholdPair Row levelCount dimension} :
    pair ∈ realizedStrongPairsOn family activeRows levelCount dimension ↔
      pair.rows.Nonempty ∧ pair.rows ⊆ activeRows ∧
        pair.IsStronglyShatteredBy (finiteClassEvaluation family) := by
  classical
  simp [realizedStrongPairsOn]

/-- The realized set is bounded by the exact ambient threshold-pair count. -/
theorem card_realizedStrongPairsOn_le
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    (family : Finset (Row → ℕ)) (activeRows : Finset Row)
    (levelCount dimension : ℕ) :
    (realizedStrongPairsOn family activeRows levelCount dimension).card ≤
      strongShatteringPairBound (Fintype.card Row) levelCount dimension := by
  classical
  calc
    (realizedStrongPairsOn family activeRows levelCount dimension).card ≤
        (Finset.univ : Finset
          (BoundedThresholdPair Row levelCount dimension)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = Fintype.card (BoundedThresholdPair Row levelCount dimension) :=
      Finset.card_univ
    _ = strongShatteringPairBound (Fintype.card Row) levelCount dimension :=
      card_boundedThresholdPair Row levelCount dimension

/-- Enlarging the finite function class can only add realized strong pairs. -/
theorem realizedStrongPairsOn_mono_family
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {small large : Finset (Row → ℕ)} {activeRows : Finset Row}
    {levelCount dimension : ℕ}
    (hsubset : small ⊆ large) :
    realizedStrongPairsOn small activeRows levelCount dimension ⊆
      realizedStrongPairsOn large activeRows levelCount dimension := by
  intro pair hpair
  rw [mem_realizedStrongPairsOn] at hpair ⊢
  exact ⟨hpair.1, hpair.2.1, hpair.2.2.mono_finiteClass hsubset⟩

/-- Enlarging the active row set can only add eligible realized pairs. -/
theorem realizedStrongPairsOn_mono_rows
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {family : Finset (Row → ℕ)} {smallRows largeRows : Finset Row}
    {levelCount dimension : ℕ}
    (hsubset : smallRows ⊆ largeRows) :
    realizedStrongPairsOn family smallRows levelCount dimension ⊆
      realizedStrongPairsOn family largeRows levelCount dimension := by
  intro pair hpair
  rw [mem_realizedStrongPairsOn] at hpair ⊢
  exact ⟨hpair.1, hpair.2.1.trans hsubset, hpair.2.2⟩

/-- A coordinate fiber realizes only pairs already realized by the original
class (on the same active rows). -/
theorem realizedStrongPairsOn_coordinateFiber_subset
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    (family : Finset (Row → ℕ)) (activeRows : Finset Row)
    (row : Row) (level : ℕ) (levelCount dimension : ℕ) :
    realizedStrongPairsOn (coordinateFiber family row level)
        activeRows levelCount dimension ⊆
      realizedStrongPairsOn family activeRows levelCount dimension := by
  apply realizedStrongPairsOn_mono_family
  intro f hf
  exact (mem_coordinateFiber.mp hf).1

end NormFormula
