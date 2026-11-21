import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.EquivFin
import NormFormula.Combinatorics.SeparatedFibers

/-!
# Finite pairing and quantitative pigeonhole lemmas

This file supplies the purely finite bookkeeping used by the strong-pair
recurrence. A sufficiently large finite family contains an injectively indexed
collection of disjoint pairs, and coding finitely many objects into a finite
type produces a code fiber at least as large as the average lower bound.
-/

namespace NormFormula

/-- Quantitative pigeonhole principle for a map between finite types. -/
theorem exists_fintype_fiber_card_ge
    {Object Code : Type*} [Fintype Object] [Fintype Code]
    [DecidableEq Object] [DecidableEq Code] [Nonempty Code]
    (code : Object → Code) (count : ℕ)
    (hcard : Fintype.card Code * count ≤ Fintype.card Object) :
    ∃ chosenCode : Code,
      count ≤ ((Finset.univ : Finset Object).filter
        fun object ↦ code object = chosenCode).card := by
  obtain ⟨chosenCode, _, hchosen⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := (Finset.univ : Finset Object))
      (t := (Finset.univ : Finset Code))
      (f := code) (n := count)
      (by simp) Finset.univ_nonempty (by simpa using hcard)
  exact ⟨chosenCode, hchosen⟩

/-- An injectively indexed collection of disjoint unordered pairs drawn from
a finite type. The two members are indexed by `Fin 2`. -/
structure FinitePairing (Item : Type*) (pairCount : ℕ) where
  selection : Fin pairCount × Fin 2 ↪ Item

/-- A finite type with at least twice `pairCount` elements admits a pairing of
that size. -/
theorem exists_finitePairing_of_two_mul_le_card
    (Item : Type*) [Fintype Item] (pairCount : ℕ)
    (hcard : 2 * pairCount ≤ Fintype.card Item) :
    Nonempty (FinitePairing Item pairCount) := by
  have hdomain : Fintype.card (Fin pairCount × Fin 2) ≤ Fintype.card Item := by
    simpa [mul_comm] using hcard
  obtain ⟨selection⟩ := Function.Embedding.nonempty_of_card_le hdomain
  exact ⟨⟨selection⟩⟩

/-- A large finite function class contains the requested number of disjoint
pairs of members. -/
theorem exists_finitePairing_subtype_of_two_mul_le_card
    {Row : Type*} [DecidableEq Row]
    (family : Finset (Row → ℕ)) (pairCount : ℕ)
    (hcard : 2 * pairCount ≤ family.card) :
    Nonempty (FinitePairing ↥family pairCount) := by
  apply exists_finitePairing_of_two_mul_le_card
  simpa using hcard

/-- A disjoint pairing in a pairwise two-separated bounded-range function
class contains a large collection of pairs sharing one separating row and the
same ordered low/high levels. The two members of an individual pair may occur
in either orientation. -/
theorem FinitePairing.exists_large_fixed_separation_code
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {family : Finset (Row → ℕ)} {rows : Finset Row}
    {pairCount levelCount count : ℕ}
    (pairing : FinitePairing ↥family pairCount)
    (hrows : rows.Nonempty) (hlevelCount : 0 < levelCount)
    (hcountPos : 0 < count)
    (hseparated : IsPairwiseTwoSeparatedOn family rows)
    (hbounded : ∀ f ∈ family, ∀ row ∈ rows, f row < levelCount)
    (hcount : (rows.card * levelCount * levelCount) * count ≤ pairCount) :
    ∃ row ∈ rows, ∃ lowLevel highLevel : ℕ,
      lowLevel < levelCount ∧ highLevel < levelCount ∧
      lowLevel + 2 ≤ highLevel ∧
      ∃ indices : Finset (Fin pairCount), count ≤ indices.card ∧
        ∀ index ∈ indices,
          ((pairing.selection (index, 0)).1 row = lowLevel ∧
            (pairing.selection (index, 1)).1 row = highLevel) ∨
          ((pairing.selection (index, 1)).1 row = lowLevel ∧
            (pairing.selection (index, 0)).1 row = highLevel) := by
  classical
  let Code := ↥rows × Fin levelCount × Fin levelCount
  obtain ⟨someRow, hsomeRow⟩ := hrows
  letI : Nonempty ↥rows := ⟨⟨someRow, hsomeRow⟩⟩
  letI : Nonempty (Fin levelCount) := ⟨⟨0, hlevelCount⟩⟩
  have hpair : ∀ index : Fin pairCount, ∃ code : Code,
      (((pairing.selection (index, 0)).1 code.1.1 = code.2.1.1 ∧
          (pairing.selection (index, 1)).1 code.1.1 = code.2.2.1) ∨
        ((pairing.selection (index, 1)).1 code.1.1 = code.2.1.1 ∧
          (pairing.selection (index, 0)).1 code.1.1 = code.2.2.1)) ∧
      code.2.1.1 + 2 ≤ code.2.2.1 := by
    intro index
    let left := pairing.selection (index, 0)
    let right := pairing.selection (index, 1)
    have hleftRight : left.1 ≠ right.1 := by
      intro heq
      have hsubtype : left = right := Subtype.ext heq
      have hindex := pairing.selection.injective hsubtype
      have hslots := congrArg Prod.snd hindex
      norm_num at hslots
    obtain ⟨row, hrow, hgap⟩ :=
      hseparated left.1 left.2 right.1 right.2 hleftRight
    let leftLevel : Fin levelCount :=
      ⟨left.1 row, hbounded left.1 left.2 row hrow⟩
    let rightLevel : Fin levelCount :=
      ⟨right.1 row, hbounded right.1 right.2 row hrow⟩
    rcases hgap with hgap | hgap
    · refine ⟨(⟨row, hrow⟩, leftLevel, rightLevel), ?_, hgap⟩
      exact Or.inl ⟨rfl, rfl⟩
    · refine ⟨(⟨row, hrow⟩, rightLevel, leftLevel), ?_, hgap⟩
      exact Or.inr ⟨rfl, rfl⟩
  choose code hcode using hpair
  have hcodeCard : Fintype.card Code * count ≤ Fintype.card (Fin pairCount) := by
    simpa [Code, mul_assoc] using hcount
  obtain ⟨chosenCode, hchosenCard⟩ :=
    exists_fintype_fiber_card_ge code count hcodeCard
  let indices : Finset (Fin pairCount) :=
    Finset.univ.filter fun index ↦ code index = chosenCode
  have hindicesNonempty : indices.Nonempty := by
    rw [← Finset.card_pos]
    exact hcountPos.trans_le hchosenCard
  obtain ⟨someIndex, hsomeIndex⟩ := hindicesNonempty
  have hsomeCode : code someIndex = chosenCode :=
    (Finset.mem_filter.mp hsomeIndex).2
  have hchosenGap : chosenCode.2.1.1 + 2 ≤ chosenCode.2.2.1 := by
    simpa [hsomeCode] using (hcode someIndex).2
  refine ⟨chosenCode.1.1, chosenCode.1.2, chosenCode.2.1.1,
    chosenCode.2.2.1, chosenCode.2.1.2, chosenCode.2.2.2,
    hchosenGap, indices, hchosenCard, ?_⟩
  intro index hindex
  have hcodeEq : code index = chosenCode := by
    exact (Finset.mem_filter.mp hindex).2
  have horientation := (hcode index).1
  simpa [hcodeEq] using horientation

/-- A fixed separation code realized by many disjoint pairs gives equally
large low and high coordinate fibers. -/
theorem FinitePairing.coordinateFibers_card_ge_of_fixed_code
    {Row : Type*} [DecidableEq Row]
    {family : Finset (Row → ℕ)} {pairCount count : ℕ}
    (pairing : FinitePairing ↥family pairCount)
    {row : Row} {lowLevel highLevel : ℕ}
    {indices : Finset (Fin pairCount)}
    (hlevels : lowLevel + 2 ≤ highLevel)
    (hcount : count ≤ indices.card)
    (horientation : ∀ index ∈ indices,
      ((pairing.selection (index, 0)).1 row = lowLevel ∧
        (pairing.selection (index, 1)).1 row = highLevel) ∨
      ((pairing.selection (index, 1)).1 row = lowLevel ∧
        (pairing.selection (index, 0)).1 row = highLevel)) :
    count ≤ (coordinateFiber family row lowLevel).card ∧
      count ≤ (coordinateFiber family row highLevel).card := by
  classical
  let lowSlot : Fin pairCount → Fin 2 := fun index ↦
    if (pairing.selection (index, 0)).1 row = lowLevel then 0 else 1
  let highSlot : Fin pairCount → Fin 2 := fun index ↦
    if (pairing.selection (index, 0)).1 row = lowLevel then 1 else 0
  have hlowAt : ∀ index : ↥indices,
      (pairing.selection (index.1, lowSlot index.1)).1 row = lowLevel := by
    intro index
    dsimp [lowSlot]
    split_ifs with hfirst
    · exact hfirst
    · rcases horientation index.1 index.2 with horientation | horientation
      · exact (hfirst horientation.1).elim
      · exact horientation.1
  have hhighAt : ∀ index : ↥indices,
      (pairing.selection (index.1, highSlot index.1)).1 row = highLevel := by
    intro index
    dsimp [highSlot]
    split_ifs with hfirst
    · rcases horientation index.1 index.2 with horientation | horientation
      · exact horientation.2
      · have heq : lowLevel = highLevel := hfirst.symm.trans horientation.2
        omega
    · rcases horientation index.1 index.2 with horientation | horientation
      · exact (hfirst horientation.1).elim
      · exact horientation.2
  let lowMap : ↥indices → ↥(coordinateFiber family row lowLevel) :=
    fun index ↦ ⟨(pairing.selection (index.1, lowSlot index.1)).1,
      mem_coordinateFiber.mpr
        ⟨(pairing.selection (index.1, lowSlot index.1)).2, hlowAt index⟩⟩
  let highMap : ↥indices → ↥(coordinateFiber family row highLevel) :=
    fun index ↦ ⟨(pairing.selection (index.1, highSlot index.1)).1,
      mem_coordinateFiber.mpr
        ⟨(pairing.selection (index.1, highSlot index.1)).2, hhighAt index⟩⟩
  have hlowInjective : Function.Injective lowMap := by
    intro i j hij
    apply Subtype.ext
    have hselected :
        pairing.selection (i.1, lowSlot i.1) =
          pairing.selection (j.1, lowSlot j.1) := by
      apply Subtype.ext
      have hfunction := congrArg Subtype.val hij
      change (pairing.selection (i.1, lowSlot i.1)).1 =
        (pairing.selection (j.1, lowSlot j.1)).1 at hfunction
      exact hfunction
    exact congrArg Prod.fst (pairing.selection.injective hselected)
  have hhighInjective : Function.Injective highMap := by
    intro i j hij
    apply Subtype.ext
    have hselected :
        pairing.selection (i.1, highSlot i.1) =
          pairing.selection (j.1, highSlot j.1) := by
      apply Subtype.ext
      have hfunction := congrArg Subtype.val hij
      change (pairing.selection (i.1, highSlot i.1)).1 =
        (pairing.selection (j.1, highSlot j.1)).1 at hfunction
      exact hfunction
    exact congrArg Prod.fst (pairing.selection.injective hselected)
  constructor
  · refine hcount.trans ?_
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective lowMap hlowInjective
  · refine hcount.trans ?_
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective highMap hhighInjective

/-- Pairing plus pigeonhole extraction produces two large coordinate fibers
at levels separated by at least two. -/
theorem FinitePairing.exists_large_separated_coordinateFibers
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {family : Finset (Row → ℕ)} {rows : Finset Row}
    {pairCount levelCount count : ℕ}
    (pairing : FinitePairing ↥family pairCount)
    (hrows : rows.Nonempty) (hlevelCount : 0 < levelCount)
    (hcountPos : 0 < count)
    (hseparated : IsPairwiseTwoSeparatedOn family rows)
    (hbounded : ∀ f ∈ family, ∀ row ∈ rows, f row < levelCount)
    (hcount : (rows.card * levelCount * levelCount) * count ≤ pairCount) :
    ∃ row ∈ rows, ∃ lowLevel highLevel : ℕ,
      lowLevel < levelCount ∧ highLevel < levelCount ∧
      lowLevel + 2 ≤ highLevel ∧
      count ≤ (coordinateFiber family row lowLevel).card ∧
      count ≤ (coordinateFiber family row highLevel).card := by
  obtain ⟨row, hrow, lowLevel, highLevel, hlowBound, hhighBound,
    hlevels, indices, hindices, horientation⟩ :=
    pairing.exists_large_fixed_separation_code hrows hlevelCount hcountPos
      hseparated hbounded hcount
  obtain ⟨hlowCard, hhighCard⟩ :=
    pairing.coordinateFibers_card_ge_of_fixed_code hlevels hindices horientation
  exact ⟨row, hrow, lowLevel, highLevel, hlowBound, hhighBound,
    hlevels, hlowCard, hhighCard⟩

/-- Direct finite-class form of the pairing-and-pigeonhole extraction. The
factor `2` pairs the class, while `rows.card * levelCount^2` bounds the ordered
separation codes. -/
theorem exists_large_separated_coordinateFibers_of_card
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {family : Finset (Row → ℕ)} {rows : Finset Row}
    {levelCount count : ℕ}
    (hrows : rows.Nonempty) (hlevelCount : 0 < levelCount)
    (hcountPos : 0 < count)
    (hseparated : IsPairwiseTwoSeparatedOn family rows)
    (hbounded : ∀ f ∈ family, ∀ row ∈ rows, f row < levelCount)
    (hcard : 2 * ((rows.card * levelCount * levelCount) * count) ≤
      family.card) :
    ∃ row ∈ rows, ∃ lowLevel highLevel : ℕ,
      lowLevel < levelCount ∧ highLevel < levelCount ∧
      lowLevel + 2 ≤ highLevel ∧
      count ≤ (coordinateFiber family row lowLevel).card ∧
      count ≤ (coordinateFiber family row highLevel).card := by
  let pairCount := (rows.card * levelCount * levelCount) * count
  obtain ⟨pairing⟩ :=
    exists_finitePairing_subtype_of_two_mul_le_card family pairCount hcard
  apply pairing.exists_large_separated_coordinateFibers
    hrows hlevelCount hcountPos hseparated hbounded
  rfl

end NormFormula
