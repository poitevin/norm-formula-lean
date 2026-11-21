import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.DeriveFintype

/-!
# Sparse coordinate order types

This file isolates the discrete part of the paper's sparse trace argument.
We collect the numerical indices occurring in a finite family of row supports
and encode each labelled parameter coordinate by

* the copy of `ℓ₂` in which it occurs;
* either the protected index to which it is equal or the gap containing it;
* all pairwise order/equality relations among parameter labels.

For `ℓ` labels and a protected set `D`, the number of such codes is a
constant depending on `ℓ` times `(2 * |D| + 1) ^ ℓ`.
-/

namespace NormFormula.HalfGraph

open scoped BigOperators

/-- The union of the numerical supports of a finite family of rows. -/
def rowIndexSet {ι : Type*} [Fintype ι] (support : ι → Finset ℕ) : Finset ℕ :=
  Finset.univ.biUnion support

/-- If each row uses at most `m` numerical indices, their union uses at most
`|ι| * m` indices. -/
theorem card_rowIndexSet_le {ι : Type*} [Fintype ι] (support : ι → Finset ℕ) (m : ℕ)
    (hsupport : ∀ i, (support i).card ≤ m) :
    (rowIndexSet support).card ≤ Fintype.card ι * m := by
  unfold rowIndexSet
  exact Finset.card_biUnion_le_card_mul Finset.univ support m (fun i _ ↦ hsupport i)

/-- Add an initial protected block to a finite set of row indices. -/
def protectedIndexSet (D : Finset ℕ) (r : ℕ) : Finset ℕ :=
  D ∪ Finset.range r

theorem card_protectedIndexSet_le (D : Finset ℕ) (r : ℕ) :
    (protectedIndexSet D r).card ≤ D.card + r := by
  exact (Finset.card_union_le D (Finset.range r)).trans_eq (by simp)

/-- The protected set formed from sparse rows has the linear cardinality
bound used in the manuscript. -/
theorem card_protectedRowIndexSet_le {ι : Type*} [Fintype ι]
    (support : ι → Finset ℕ) (m r : ℕ) (hsupport : ∀ i, (support i).card ≤ m) :
    (protectedIndexSet (rowIndexSet support) r).card ≤ Fintype.card ι * m + r := by
  exact (card_protectedIndexSet_le (rowIndexSet support) r).trans
    (Nat.add_le_add_right (card_rowIndexSet_le support m hsupport) r)

/-- Which copy of `ℓ₂` contains a labelled coordinate. -/
inductive CoordinateCopy
  | first
  | second
  deriving DecidableEq, Fintype

@[simp]
theorem card_coordinateCopy : Fintype.card CoordinateCopy = 2 := by decide

/-- The three possible order/equality relations between two indices. -/
inductive NatOrderRelation
  | lt
  | eq
  | gt
  deriving DecidableEq, Fintype

@[simp]
theorem card_natOrderRelation : Fintype.card NatOrderRelation = 3 := by decide

/-- The order relation between two natural-number indices. -/
def natOrderRelation (i j : ℕ) : NatOrderRelation :=
  if i < j then .lt else if i = j then .eq else .gt

/-- The protected indices lying strictly below `i`. -/
def lowerIndices (D : Finset ℕ) (i : ℕ) : Finset ℕ :=
  D.filter fun d ↦ d < i

@[simp]
theorem mem_lowerIndices {D : Finset ℕ} {i d : ℕ} :
    d ∈ lowerIndices D i ↔ d ∈ D ∧ d < i := by
  simp [lowerIndices]

/-- A numerical index is either equal to a protected index or lies in one of
the `|D| + 1` complementary gaps. -/
abbrev RelativePosition (D : Finset ℕ) :=
  D ⊕ Fin (D.card + 1)

@[simp]
theorem card_relativePosition (D : Finset ℕ) :
    Fintype.card (RelativePosition D) = 2 * D.card + 1 := by
  simp [RelativePosition]
  omega

/-- Encode the position of `i` relative to the protected set `D`. -/
def relativePosition (D : Finset ℕ) (i : ℕ) : RelativePosition D :=
  if hi : i ∈ D then
    Sum.inl ⟨i, hi⟩
  else
    Sum.inr ⟨(lowerIndices D i).card, Nat.lt_succ_of_le (Finset.card_le_card (by
      intro d hd
      exact (mem_lowerIndices.mp hd).1))⟩

/-- Equal gap codes have the same lower protected segment. -/
private theorem lowerIndices_eq_of_relativePosition_eq {D : Finset ℕ} {i j : ℕ}
    (hi : i ∉ D) (hj : j ∉ D) (hpos : relativePosition D i = relativePosition D j) :
    lowerIndices D i = lowerIndices D j := by
  have hcard : (lowerIndices D i).card = (lowerIndices D j).card := by
    simpa [relativePosition, hi, hj] using hpos
  rcases le_total i j with hij | hji
  · apply Finset.eq_of_subset_of_card_le
    · intro d hd
      exact mem_lowerIndices.mpr ⟨(mem_lowerIndices.mp hd).1, (mem_lowerIndices.mp hd).2.trans_le hij⟩
    · exact hcard.ge
  · symm
    apply Finset.eq_of_subset_of_card_le
    · intro d hd
      exact mem_lowerIndices.mpr ⟨(mem_lowerIndices.mp hd).1, (mem_lowerIndices.mp hd).2.trans_le hji⟩
    · exact hcard.le

/-- The relative-position code determines every order and equality relation
with the protected set. -/
theorem relativePosition_eq_preserves_relations {D : Finset ℕ} {i j d : ℕ}
    (hpos : relativePosition D i = relativePosition D j) (hd : d ∈ D) :
    (i < d ↔ j < d) ∧ (i = d ↔ j = d) ∧ (d < i ↔ d < j) := by
  by_cases hi : i ∈ D
  · have hj : j ∈ D := by
      by_contra hj
      simp [relativePosition, hi, hj] at hpos
    have hij : i = j := by
      simpa [relativePosition, hi, hj] using hpos
    subst j
    simp
  · have hj : j ∉ D := by
      intro hj
      simp [relativePosition, hi, hj] at hpos
    have hlower := lowerIndices_eq_of_relativePosition_eq hi hj hpos
    have hbelow : d < i ↔ d < j := by
      have hmem := Finset.ext_iff.mp hlower d
      simpa [mem_lowerIndices, hd] using hmem
    have hid : i ≠ d := fun h ↦ hi (h ▸ hd)
    have hjd : j ≠ d := fun h ↦ hj (h ▸ hd)
    constructor
    · omega
    · exact ⟨by simp [hid, hjd], hbelow⟩

/-- The discrete type of `ℓ` labelled parameter coordinates relative to `D`.
The final factor records pairwise relations among the labels. -/
abbrev SparseOrderType (D : Finset ℕ) (ℓ : ℕ) :=
  (Fin ℓ → CoordinateCopy) ×
    ((Fin ℓ → RelativePosition D) ×
      (Fin ℓ → Fin ℓ → NatOrderRelation))

/-- Construct the discrete type of labelled parameter coordinates. -/
def sparseOrderType (D : Finset ℕ) {ℓ : ℕ}
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ) : SparseOrderType D ℓ :=
  ⟨copy, ⟨fun a ↦ relativePosition D (index a),
    fun a b ↦ natOrderRelation (index a) (index b)⟩⟩

/-- Equal sparse order types preserve the copy containing every label. -/
theorem sparseOrderType_eq_preserves_copy {D : Finset ℕ} {ℓ : ℕ}
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index') (a : Fin ℓ) :
    copy a = copy' a := by
  exact congrFun (congrArg Prod.fst h) a

/-- Equal sparse order types preserve all pairwise label relations. -/
theorem sparseOrderType_eq_preserves_pair_relation {D : Finset ℕ} {ℓ : ℕ}
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index') (a b : Fin ℓ) :
    natOrderRelation (index a) (index b) = natOrderRelation (index' a) (index' b) := by
  exact congrFun (congrFun (congrArg (fun t ↦ t.2.2) h) a) b

/-- Equal sparse order types preserve every relation between a parameter
label and a protected row index. -/
theorem sparseOrderType_eq_preserves_protected_relations {D : Finset ℕ} {ℓ : ℕ}
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index')
    (a : Fin ℓ) {d : ℕ} (hd : d ∈ D) :
    (index a < d ↔ index' a < d) ∧
      (index a = d ↔ index' a = d) ∧
      (d < index a ↔ d < index' a) := by
  apply relativePosition_eq_preserves_relations _ hd
  exact congrFun (congrArg (fun t ↦ t.2.1) h) a

/-- The factor independent of the protected set in the order-type count. -/
def orderTypeConstant (ℓ : ℕ) : ℕ :=
  2 ^ ℓ * 3 ^ (ℓ * ℓ)

/-- Exact cardinality of the ambient discrete-code space. -/
theorem card_sparseOrderType (D : Finset ℕ) (ℓ : ℕ) :
    Fintype.card (SparseOrderType D ℓ) =
      orderTypeConstant ℓ * (2 * D.card + 1) ^ ℓ := by
  simp only [SparseOrderType, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    card_coordinateCopy, card_relativePosition, card_natOrderRelation, orderTypeConstant]
  rw [← pow_mul]
  ring

/-- Consequently, a linear bound on `|D|` gives a polynomial order-type
bound of degree `ℓ`. -/
theorem card_sparseOrderType_le (D : Finset ℕ) (ℓ B : ℕ) (hD : D.card ≤ B) :
    Fintype.card (SparseOrderType D ℓ) ≤
      orderTypeConstant ℓ * (2 * B + 1) ^ ℓ := by
  rw [card_sparseOrderType]
  exact Nat.mul_le_mul_left _ (pow_le_pow_left' (by omega) ℓ)

/-- Substituting the sparse-row union bound gives the polynomial estimate in
the number of rows. -/
theorem card_sparseOrderType_protectedRow_le {ι : Type*} [Fintype ι]
    (support : ι → Finset ℕ) (m r ℓ : ℕ) (hsupport : ∀ i, (support i).card ≤ m) :
    Fintype.card (SparseOrderType (protectedIndexSet (rowIndexSet support) r) ℓ) ≤
      orderTypeConstant ℓ * (2 * (Fintype.card ι * m + r) + 1) ^ ℓ := by
  exact card_sparseOrderType_le _ ℓ _
    (card_protectedRowIndexSet_le support m r hsupport)

end NormFormula.HalfGraph
