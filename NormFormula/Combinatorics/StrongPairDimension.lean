import NormFormula.Combinatorics.StrongPairIteration

/-!
# Reindexing realized strong pairs by a dimension bound

The recurrence counts pairs in the ambient encoding whose dimension bound is
the full row cardinality. To compare this count with a smaller finite strong-
shattering dimension, we canonically reindex every pair whose support has size
at most `d` into the dimension-`d` encoding and prove that reindexing is
injective.
-/

namespace NormFormula

/-- Re-encode a bounded threshold pair using any dimension bound large enough
for its actual row support. -/
def BoundedThresholdPair.reindexDimension
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {levelCount sourceDimension targetDimension : ℕ}
    (pair : BoundedThresholdPair Row levelCount sourceDimension)
    (hcard : pair.rows.card ≤ targetDimension) :
    BoundedThresholdPair Row levelCount targetDimension := by
  let newSize : Fin (targetDimension + 1) :=
    ⟨pair.rows.card, Nat.lt_succ_of_le hcard⟩
  let newRows :
      ↥((Finset.univ : Finset Row).powersetCard newSize) :=
    ⟨pair.rows, by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, rfl⟩⟩
  let newThreshold : ↥(newRows : Finset Row) → Fin levelCount :=
    fun row ↦ pair.2.2 ⟨row.1, row.2⟩
  exact ⟨newSize, newRows, newThreshold⟩

@[simp] theorem BoundedThresholdPair.reindexDimension_rows
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {levelCount sourceDimension targetDimension : ℕ}
    (pair : BoundedThresholdPair Row levelCount sourceDimension)
    (hcard : pair.rows.card ≤ targetDimension) :
    (pair.reindexDimension hcard).rows = pair.rows := by
  rfl

@[simp] theorem BoundedThresholdPair.reindexDimension_threshold
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {levelCount sourceDimension targetDimension : ℕ}
    (pair : BoundedThresholdPair Row levelCount sourceDimension)
    (hcard : pair.rows.card ≤ targetDimension) :
    (pair.reindexDimension hcard).threshold = pair.threshold := by
  funext row
  by_cases hrow : row ∈ pair.rows
  · rw [BoundedThresholdPair.threshold_apply_of_mem _ (by simpa using hrow),
      BoundedThresholdPair.threshold_apply_of_mem pair hrow]
    rfl
  · simp [BoundedThresholdPair.threshold, hrow]

/-- Reindexing is injective on the underlying pairs; the proofs of the target
dimension bound are immaterial. -/
theorem BoundedThresholdPair.reindexDimension_injective
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {levelCount sourceDimension targetDimension : ℕ}
    {p q : BoundedThresholdPair Row levelCount sourceDimension}
    (hp : p.rows.card ≤ targetDimension)
    (hq : q.rows.card ≤ targetDimension)
    (heq : p.reindexDimension hp = q.reindexDimension hq) :
    p = q := by
  apply BoundedThresholdPair.ext_rows_threshold
  · have hrows := congrArg BoundedThresholdPair.rows heq
    simpa using hrows
  · have hthreshold := congrArg BoundedThresholdPair.threshold heq
    simpa using hthreshold

/-- If every pair realized in the full-row encoding has support of size at
most `dimension`, its cardinality is bounded by the exact dimension-`d`
threshold-pair count. -/
theorem card_realizedStrongPairsOn_le_of_card_rows_le
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    (family : Finset (Row → ℕ)) (activeRows : Finset Row)
    (levelCount dimension : ℕ)
    (hdimension : ∀ pair ∈ realizedStrongPairsOn family activeRows
        levelCount (Fintype.card Row), pair.rows.card ≤ dimension) :
    (realizedStrongPairsOn family activeRows levelCount
        (Fintype.card Row)).card ≤
      strongShatteringPairBound (Fintype.card Row) levelCount dimension := by
  classical
  let source := realizedStrongPairsOn family activeRows levelCount
    (Fintype.card Row)
  let reindex : ↥source → BoundedThresholdPair Row levelCount dimension :=
    fun pair ↦ pair.1.reindexDimension (hdimension pair.1 pair.2)
  have hreindex : Function.Injective reindex := by
    intro p q hpq
    apply Subtype.ext
    exact BoundedThresholdPair.reindexDimension_injective
      (hdimension p.1 p.2) (hdimension q.1 q.2) hpq
  change source.card ≤
    strongShatteringPairBound (Fintype.card Row) levelCount dimension
  calc
    source.card = Fintype.card ↥source :=
      (Fintype.card_coe source).symm
    _ ≤ Fintype.card (BoundedThresholdPair Row levelCount dimension) :=
      Fintype.card_le_of_injective reindex hreindex
    _ = strongShatteringPairBound (Fintype.card Row) levelCount dimension :=
      card_boundedThresholdPair Row levelCount dimension

end NormFormula
