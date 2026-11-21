import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import NormFormula.Analytic.HalfGraphSeminorm

/-!
# A finite maximum formula for the ordered-pair seminorm

For a pair of finitely supported sequences, the supremum defining `q` is the
maximum of a finite list.  Besides values using two support coordinates, the
list contains the one-coordinate values which arise by pairing a support
coordinate with a zero coordinate in the other copy.
-/

namespace NormFormula.HalfGraph

/-- There is a zero first-copy support position strictly before `b`. -/
def hasZeroBefore (A : Finset ℕ) (b : ℕ) : Prop :=
  ∃ a, a < b ∧ a ∉ A

/-- Values arising from admissible pairs meeting both supports. -/
noncomputable def pairedQValues (u v : RealL2) (A B : Finset ℕ) : Finset ℝ :=
  A.biUnion fun a ↦
    (B.filter fun b ↦ a < b).image fun b ↦ |u a + v b|

/-- Values arising from a first-copy support coordinate paired with a zero
second-copy coordinate farther to the right. -/
noncomputable def firstOnlyQValues (u : RealL2) (A : Finset ℕ) : Finset ℝ :=
  A.image fun a ↦ |u a|

/-- Values arising from a second-copy support coordinate which has a zero
first-copy position before it. -/
noncomputable def secondOnlyQValues (v : RealL2) (A B : Finset ℕ) : Finset ℝ := by
  classical
  exact (B.filter fun b ↦ hasZeroBefore A b).image fun b ↦ |v b|

/-- The finite list whose maximum computes `q` for the supplied supports. -/
noncomputable def finiteQValues (u v : RealL2) (A B : Finset ℕ) : Finset ℝ :=
  insert 0 (pairedQValues u v A B ∪ firstOnlyQValues u A ∪ secondOnlyQValues v A B)

theorem finiteQValues_nonempty (u v : RealL2) (A B : Finset ℕ) :
    (finiteQValues u v A B).Nonempty := by
  exact ⟨0, by simp [finiteQValues]⟩

/-- A genuine ordered pair is bounded by the supremum defining `q`. -/
theorem orderedPairValue_le_q (u v : RealL2) {i j : ℕ} (hij : i < j) :
    |u i + v j| ≤ qSeminorm (WithLp.toLp 2 (u, v)) := by
  rw [qSeminorm_apply]
  let p : OrderedPair := ⟨(i, j), hij⟩
  have hbdd : BddAbove
      (Set.range fun p : OrderedPair ↦
        |(WithLp.toLp 2 (u, v)).fst p.1.1 + (WithLp.toLp 2 (u, v)).snd p.1.2|) := by
    refine ⟨Real.sqrt 2 * ‖WithLp.toLp 2 (u, v)‖, ?_⟩
    rintro _ ⟨r, rfl⟩
    simpa [pairSeminorm_apply] using
      pairSeminorm_le_sqrtTwo_mul_norm r.1.1 r.1.2 (WithLp.toLp 2 (u, v))
  simpa [p] using le_ciSup hbdd p

/-- A value using one coordinate from each support belongs to the finite list. -/
theorem pairedQValue_mem_finiteQValues (u v : RealL2) (A B : Finset ℕ)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ B) (hab : a < b) :
    |u a + v b| ∈ finiteQValues u v A B := by
  classical
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [pairedQValues, Finset.mem_biUnion]
  exact ⟨a, ha, Finset.mem_image.mpr
    ⟨b, Finset.mem_filter.mpr ⟨hb, hab⟩, rfl⟩⟩

/-- A first-copy one-coordinate value belongs to the finite list. -/
theorem firstOnlyQValue_mem_finiteQValues (u v : RealL2) (A B : Finset ℕ)
    {a : ℕ} (ha : a ∈ A) : |u a| ∈ finiteQValues u v A B := by
  classical
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  rw [firstOnlyQValues, Finset.mem_image]
  exact ⟨a, ha, rfl⟩

/-- A second-copy one-coordinate value with an earlier zero position belongs
to the finite list. -/
theorem secondOnlyQValue_mem_finiteQValues (u v : RealL2) (A B : Finset ℕ)
    {b : ℕ} (hb : b ∈ B) (hzero : hasZeroBefore A b) :
    |v b| ∈ finiteQValues u v A B := by
  classical
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_right
  rw [secondOnlyQValues, Finset.mem_image]
  exact ⟨b, Finset.mem_filter.mpr ⟨hb, hzero⟩, rfl⟩

/-- Every admissible pair value belongs to the finite list when `A` and `B`
contain the supports. They need not be exact: a candidate coordinate may
cancel to zero. -/
theorem orderedPairValue_mem_finiteQValues_of_support_subset
    (u v : RealL2) (A B : Finset ℕ)
    (hA : ∀ i, i ∉ A → u i = 0) (hB : ∀ j, j ∉ B → v j = 0)
    {i j : ℕ} (hij : i < j) :
    |u i + v j| ∈ finiteQValues u v A B := by
  classical
  by_cases hiA : i ∈ A
  · by_cases hjB : j ∈ B
    · exact pairedQValue_mem_finiteQValues u v A B hiA hjB hij
    · have hvj : v j = 0 := hB j hjB
      rw [hvj, add_zero]
      exact firstOnlyQValue_mem_finiteQValues u v A B hiA
  · have hui : u i = 0 := hA i hiA
    by_cases hjB : j ∈ B
    · have hzero : hasZeroBefore A j := ⟨i, hij, hiA⟩
      rw [hui, zero_add]
      exact secondOnlyQValue_mem_finiteQValues u v A B hjB hzero
    · have hvj : v j = 0 := hB j hjB
      simp [finiteQValues, hui, hvj]

/-- Exact supports are a special case of support containment. -/
theorem orderedPairValue_mem_finiteQValues (u v : RealL2) (A B : Finset ℕ)
    (hA : ∀ i, i ∈ A ↔ u i ≠ 0) (hB : ∀ j, j ∈ B ↔ v j ≠ 0)
    {i j : ℕ} (hij : i < j) :
    |u i + v j| ∈ finiteQValues u v A B := by
  apply orderedPairValue_mem_finiteQValues_of_support_subset u v A B
  · intro a ha
    by_contra hua
    exact ha ((hA a).2 hua)
  · intro b hb
    by_contra hvb
    exact hb ((hB b).2 hvb)
  · exact hij

/-- A first-copy one-coordinate value is realized by an admissible pair,
using a zero coordinate beyond the finite second support. -/
theorem firstOnlyValue_le_q (u v : RealL2) (B : Finset ℕ) (a : ℕ)
    (hB : ∀ j, j ∉ B → v j = 0) :
    |u a| ≤ qSeminorm (WithLp.toLp 2 (u, v)) := by
  let j := max a (B.sup id) + 1
  have haj : a < j := by
    dsimp [j]
    omega
  have hjB : j ∉ B := by
    intro hjB
    have hjle : j ≤ B.sup id := Finset.le_sup (f := id) hjB
    dsimp [j] at hjle
    omega
  have hvj : v j = 0 := hB j hjB
  simpa [hvj] using orderedPairValue_le_q u v haj

/-- The finite list has a size bounded only by the two support sizes. -/
theorem card_finiteQValues_le (u v : RealL2) (A B : Finset ℕ) :
    (finiteQValues u v A B).card ≤
      1 + A.card * B.card + A.card + B.card := by
  classical
  have hpair : (pairedQValues u v A B).card ≤ A.card * B.card := by
    apply Finset.card_biUnion_le_card_mul A
      (fun a ↦ (B.filter fun b ↦ a < b).image fun b ↦ |u a + v b|) B.card
    intro a ha
    exact Finset.card_image_le.trans (Finset.card_filter_le B (fun b ↦ a < b))
  have hfirst : (firstOnlyQValues u A).card ≤ A.card := by
    exact Finset.card_image_le
  have hsecond : (secondOnlyQValues v A B).card ≤ B.card := by
    exact Finset.card_image_le.trans
      (Finset.card_filter_le B (fun b ↦ hasZeroBefore A b))
  have hunionPF :
      (pairedQValues u v A B ∪ firstOnlyQValues u A).card ≤
        (pairedQValues u v A B).card + (firstOnlyQValues u A).card :=
    Finset.card_union_le _ _
  have hunionAll :
      (pairedQValues u v A B ∪ firstOnlyQValues u A ∪
        secondOnlyQValues v A B).card ≤
      (pairedQValues u v A B ∪ firstOnlyQValues u A).card +
        (secondOnlyQValues v A B).card :=
    Finset.card_union_le _ _
  unfold finiteQValues
  calc
    _ ≤ (pairedQValues u v A B ∪ firstOnlyQValues u A ∪
        secondOnlyQValues v A B).card + 1 := Finset.card_insert_le _ _
    _ ≤ ((pairedQValues u v A B ∪ firstOnlyQValues u A).card +
        (secondOnlyQValues v A B).card) + 1 := by
          exact Nat.add_le_add_right hunionAll 1
    _ ≤ (((pairedQValues u v A B).card + (firstOnlyQValues u A).card) +
        (secondOnlyQValues v A B).card) + 1 := by
          exact Nat.add_le_add_right (Nat.add_le_add_right hunionPF _) 1
    _ ≤ 1 + A.card * B.card + A.card + B.card := by
          omega

/-- The maximum formula is stable under cancellations: it is enough that
`A` and `B` contain the supports. A vanishing candidate first coordinate
turns a retained two-coordinate entry into the required second-only entry. -/
theorem qSeminorm_eq_max_finiteQValues_of_support_subset
    (u v : RealL2) (A B : Finset ℕ)
    (hA : ∀ i, i ∉ A → u i = 0) (hB : ∀ j, j ∉ B → v j = 0) :
    qSeminorm (WithLp.toLp 2 (u, v)) =
      (finiteQValues u v A B).max' (finiteQValues_nonempty u v A B) := by
  classical
  let values := finiteQValues u v A B
  apply le_antisymm
  · rw [qSeminorm_apply]
    refine ciSup_le fun p ↦ ?_
    exact Finset.le_max' values _
      (orderedPairValue_mem_finiteQValues_of_support_subset u v A B hA hB p.2)
  · rw [Finset.max'_le_iff]
    intro c hc
    change c ∈ finiteQValues u v A B at hc
    rw [finiteQValues, Finset.mem_insert] at hc
    rcases hc with rfl | hc
    · exact apply_nonneg qSeminorm _
    rcases Finset.mem_union.mp hc with hpf | hsecond
    · rcases Finset.mem_union.mp hpf with hpair | hfirst
      · rw [pairedQValues] at hpair
        rcases Finset.mem_biUnion.mp hpair with ⟨a, haA, ha⟩
        rcases Finset.mem_image.mp ha with ⟨b, hb, rfl⟩
        exact orderedPairValue_le_q u v (Finset.mem_filter.mp hb).2
      · rw [firstOnlyQValues] at hfirst
        rcases Finset.mem_image.mp hfirst with ⟨a, haA, rfl⟩
        exact firstOnlyValue_le_q u v B a hB
    · rw [secondOnlyQValues] at hsecond
      rcases Finset.mem_image.mp hsecond with ⟨b, hb, rfl⟩
      obtain ⟨a, hab, haA⟩ := (Finset.mem_filter.mp hb).2
      have hua : u a = 0 := hA a haA
      simpa [hua] using orderedPairValue_le_q u v hab

/-- For exact finite supports `A` and `B`, the ordered-pair seminorm is the
maximum of `finiteQValues`. -/
theorem qSeminorm_eq_max_finiteQValues (u v : RealL2) (A B : Finset ℕ)
    (hA : ∀ i, i ∈ A ↔ u i ≠ 0) (hB : ∀ j, j ∈ B ↔ v j ≠ 0) :
    qSeminorm (WithLp.toLp 2 (u, v)) =
      (finiteQValues u v A B).max' (finiteQValues_nonempty u v A B) := by
  apply qSeminorm_eq_max_finiteQValues_of_support_subset u v A B
  · intro a ha
    by_contra hua
    exact ha ((hA a).2 hua)
  · intro b hb
    by_contra hvb
    exact hb ((hB b).2 hvb)

end NormFormula.HalfGraph
