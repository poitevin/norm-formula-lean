import Mathlib.Data.Finset.Powerset
import NormFormula.Combinatorics.StrongShattering

/-!
# Counting finite strong-shattering pairs

For a finite row type, a range with `b` integer levels, and dimension bound
`d`, the possible thresholded row pairs are indexed by a row-set size
`k ≤ d`, a `k`-element row set, and one of `b^k` threshold assignments. This
file packages that dependent finite type and proves its exact cardinality.
-/

namespace NormFormula

/-- The numerical upper bound for thresholded row pairs of dimension at most
`dimension` on `rowCount` rows with `levelCount` possible threshold values. -/
def strongShatteringPairBound
    (rowCount levelCount dimension : ℕ) : ℕ :=
  ∑ k : Fin (dimension + 1),
    Nat.choose rowCount k * levelCount ^ (k : ℕ)

/-- A row set of size at most `dimension`, together with a threshold value on
each selected row. The row set is represented by its unique cardinality
index, so no pair is counted twice. -/
def BoundedThresholdPair
    (Row : Type*) [Fintype Row] [DecidableEq Row]
    (levelCount dimension : ℕ) :=
  Sigma fun k : Fin (dimension + 1) ↦
    Sigma fun rows : ↥((Finset.univ : Finset Row).powersetCard k) ↦
      (↥(rows : Finset Row) → Fin levelCount)

noncomputable instance boundedThresholdPairFintype
    (Row : Type*) [Fintype Row] [DecidableEq Row]
    (levelCount dimension : ℕ) :
    Fintype (BoundedThresholdPair Row levelCount dimension) := by
  unfold BoundedThresholdPair
  infer_instance

/-- The finite row set carried by a bounded threshold pair. -/
def BoundedThresholdPair.rows
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {levelCount dimension : ℕ}
    (pair : BoundedThresholdPair Row levelCount dimension) : Finset Row :=
  pair.2.1

/-- The selected row set has the cardinality recorded by its finite index. -/
theorem BoundedThresholdPair.card_rows
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {levelCount dimension : ℕ}
    (pair : BoundedThresholdPair Row levelCount dimension) :
    pair.rows.card = (pair.1 : ℕ) := by
  exact (Finset.mem_powersetCard.mp pair.2.1.property).2

/-- In particular, every selected row set respects the dimension bound. -/
theorem BoundedThresholdPair.card_rows_le
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {levelCount dimension : ℕ}
    (pair : BoundedThresholdPair Row levelCount dimension) :
    pair.rows.card ≤ dimension := by
  rw [pair.card_rows]
  exact Nat.lt_succ_iff.mp pair.1.isLt

/-- Extend the pair's threshold assignment by zero off its selected rows. -/
def BoundedThresholdPair.threshold
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {levelCount dimension : ℕ}
    (pair : BoundedThresholdPair Row levelCount dimension) : Row → ℕ :=
  fun row ↦ if hrow : row ∈ pair.rows then pair.2.2 ⟨row, hrow⟩ else 0

@[simp] theorem BoundedThresholdPair.threshold_apply_of_mem
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {levelCount dimension : ℕ}
    (pair : BoundedThresholdPair Row levelCount dimension)
    {row : Row} (hrow : row ∈ pair.rows) :
    pair.threshold row = pair.2.2 ⟨row, hrow⟩ := by
  simp [BoundedThresholdPair.threshold, hrow]

/-- A bounded threshold pair realized by a natural-valued evaluation class. -/
def BoundedThresholdPair.IsStronglyShatteredBy
    {Row Parameter : Type*} [Fintype Row] [DecidableEq Row]
    {levelCount dimension : ℕ}
    (pair : BoundedThresholdPair Row levelCount dimension)
    (value : Row → Parameter → ℕ) : Prop :=
  StronglyShattersAtUnit value pair.rows pair.threshold

/-- Exact count of all bounded threshold pairs. -/
theorem card_boundedThresholdPair
    (Row : Type*) [Fintype Row] [DecidableEq Row]
    (levelCount dimension : ℕ) :
    Fintype.card (BoundedThresholdPair Row levelCount dimension) =
      strongShatteringPairBound (Fintype.card Row) levelCount dimension := by
  unfold BoundedThresholdPair strongShatteringPairBound
  change Fintype.card (Sigma fun k : Fin (dimension + 1) ↦
    Sigma fun rows : ↥((Finset.univ : Finset Row).powersetCard k) ↦
      (↥(rows : Finset Row) → Fin levelCount)) = _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro k _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_fin]
  have hcard : ∀ rows : ↥((Finset.univ : Finset Row).powersetCard (k : ℕ)),
      Fintype.card ↥(rows : Finset Row) = (k : ℕ) := by
    intro rows
    rw [Fintype.card_coe]
    exact (Finset.mem_powersetCard.mp rows.property).2
  simp_rw [hcard]
  rw [Finset.sum_const, nsmul_eq_mul]
  simp [Finset.card_powersetCard]

end NormFormula
