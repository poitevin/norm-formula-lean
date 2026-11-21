import NormFormula.Combinatorics.SparseTypeTransport

/-!
# Symbolic affine lists for sparse order types

A candidate coordinate is represented symbolically either by a fixed row
support position or by a parameter label.  These slots do not move when a
sparse order type is realized at different numerical indices.  This file
assembles the pointwise transport lemmas into invariance of the entire affine
list used to compute `q`.
-/

namespace NormFormula.HalfGraph

/-- A symbolic coordinate is either a fixed row-support position or a
parameter label. -/
abbrev CoordinateSlot (rowSupport : Finset ℕ) (ℓ : ℕ) :=
  rowSupport ⊕ Fin ℓ

/-- A row slot is always active; a label slot is active in the selected copy
exactly when its copy code agrees with `target`. -/
def coordinateSlotActive {rowSupport : Finset ℕ} {ℓ : ℕ}
    (copy : Fin ℓ → CoordinateCopy) (target : CoordinateCopy) :
    CoordinateSlot rowSupport ℓ → Prop
  | .inl _ => True
  | .inr a => copy a = target

/-- The numerical position represented by a symbolic slot. -/
def coordinateSlotIndex {rowSupport : Finset ℕ} {ℓ : ℕ}
    (index : Fin ℓ → ℕ) : CoordinateSlot rowSupport ℓ → ℕ
  | .inl d => d.1
  | .inr a => index a

/-- The coordinate affine form represented by a symbolic slot. -/
def coordinateSlotForm {rowSupport : Finset ℕ} {ℓ : ℕ}
    (row : ℕ → ℝ) (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (target : CoordinateCopy) (slot : CoordinateSlot rowSupport ℓ) : AffineForm ℓ :=
  labelledCoordinateForm row copy index target (coordinateSlotIndex index slot)

/-- All active symbolic slots in one copy. -/
noncomputable def activeCoordinateSlots (rowSupport : Finset ℕ) {ℓ : ℕ}
    (copy : Fin ℓ → CoordinateCopy) (target : CoordinateCopy) :
    Finset (CoordinateSlot rowSupport ℓ) := by
  classical
  exact Finset.univ.filter (coordinateSlotActive copy target)

/-- Equal sparse types preserve whether a symbolic slot is active. -/
theorem coordinateSlotActive_iff_of_sparseOrderType_eq
    {D rowSupport : Finset ℕ} {ℓ : ℕ}
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index')
    (target : CoordinateCopy) (slot : CoordinateSlot rowSupport ℓ) :
    coordinateSlotActive copy target slot ↔
      coordinateSlotActive copy' target slot := by
  rcases slot with d | a
  · simp [coordinateSlotActive]
  · simp only [coordinateSlotActive]
    rw [sparseOrderType_eq_preserves_copy h a]

theorem activeCoordinateSlots_eq_of_sparseOrderType_eq
    {D rowSupport : Finset ℕ} {ℓ : ℕ}
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index')
    (target : CoordinateCopy) :
    activeCoordinateSlots rowSupport copy target =
      activeCoordinateSlots rowSupport copy' target := by
  ext slot
  simp only [activeCoordinateSlots, Finset.mem_filter, Finset.mem_univ, true_and]
  exact coordinateSlotActive_iff_of_sparseOrderType_eq h target slot

/-- The numerical image of the active symbolic slots is exactly the candidate
support used by `AffineQList`. -/
theorem image_activeCoordinateSlots_eq_candidateSupport
    (rowSupport : Finset ℕ) {ℓ : ℕ}
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (target : CoordinateCopy) :
    (activeCoordinateSlots rowSupport copy target).image
        (coordinateSlotIndex index) =
      candidateSupport rowSupport copy index target := by
  classical
  ext n
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨slot, hslot, hindex⟩
    rcases slot with d | a
    · rw [coordinateSlotIndex] at hindex
      rw [← hindex]
      exact Finset.mem_union_left _ d.2
    · rw [coordinateSlotIndex] at hindex
      apply Finset.mem_union_right
      rw [labelIndexSet, Finset.mem_image]
      refine ⟨a, ?_, hindex⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hslot).2⟩
  · intro hn
    rw [candidateSupport, Finset.mem_union] at hn
    rcases hn with hrow | hlabel
    · apply Finset.mem_image.mpr
      refine ⟨Sum.inl ⟨n, hrow⟩, ?_, rfl⟩
      simp [activeCoordinateSlots, coordinateSlotActive]
    · rw [labelIndexSet, Finset.mem_image] at hlabel
      rcases hlabel with ⟨a, ha, hindex⟩
      apply Finset.mem_image.mpr
      refine ⟨Sum.inr a, ?_, hindex⟩
      simp [activeCoordinateSlots, coordinateSlotActive, (Finset.mem_filter.mp ha).2]

/-- Equal sparse types preserve the strict order between any two symbolic
slots whose row positions lie in the protected set. -/
theorem coordinateSlotIndex_lt_iff_of_sparseOrderType_eq
    {D firstRowSupport secondRowSupport : Finset ℕ} {ℓ : ℕ}
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index')
    (hfirstD : firstRowSupport ⊆ D) (hsecondD : secondRowSupport ⊆ D)
    (a : CoordinateSlot firstRowSupport ℓ)
    (b : CoordinateSlot secondRowSupport ℓ) :
    coordinateSlotIndex index a < coordinateSlotIndex index b ↔
      coordinateSlotIndex index' a < coordinateSlotIndex index' b := by
  rcases a with a | a <;> rcases b with b | b
  · simp [coordinateSlotIndex]
  · exact (sparseOrderType_eq_preserves_protected_relations h b
      (hfirstD a.2)).2.2
  · exact (sparseOrderType_eq_preserves_protected_relations h a
      (hsecondD b.2)).1
  · exact sparseOrderType_eq_preserves_pair_lt h a b

/-- Equal sparse types preserve the affine form attached to a symbolic slot. -/
theorem coordinateSlotForm_eq_of_sparseOrderType_eq
    {D rowSupport : Finset ℕ} {ℓ : ℕ} (row : ℕ → ℝ)
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index')
    (hrowD : rowSupport ⊆ D) (hrow : ∀ n, n ∉ rowSupport → row n = 0)
    (target : CoordinateCopy) (slot : CoordinateSlot rowSupport ℓ) :
    coordinateSlotForm row copy index target slot =
      coordinateSlotForm row copy' index' target slot := by
  rcases slot with d | a
  · exact labelledCoordinateForm_eq_at_protected row h target (hrowD d.2)
  · exact labelledCoordinateForm_eq_at_label row h hrowD hrow target a

/-- The second-only predicate attached to a symbolic second-coordinate slot
is invariant inside one sparse order type. -/
theorem coordinateSlot_hasZeroBefore_iff_of_sparseOrderType_eq
    {D firstRowSupport secondRowSupport : Finset ℕ} {ℓ s : ℕ}
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index')
    (hsize : firstRowSupport.card + ℓ ≤ s)
    (hprotected : Finset.range (s + 1) ⊆ D)
    (slot : CoordinateSlot secondRowSupport ℓ) :
    hasZeroBefore (candidateSupport firstRowSupport copy index .first)
        (coordinateSlotIndex index slot) ↔
      hasZeroBefore (candidateSupport firstRowSupport copy' index' .first)
        (coordinateSlotIndex index' slot) := by
  rcases slot with d | a
  · exact hasZeroBefore_candidateSupport_fixed_iff h hsize hprotected d.1
  · exact hasZeroBefore_candidateSupport_label_iff h hsize hprotected a

/-- Symbolic affine forms from admissible first--second slot pairs. -/
noncomputable def symbolicPairedQForms {ℓ : ℕ}
    (rowU rowV : ℕ → ℝ) (A₀ B₀ : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ) : Finset (AffineForm ℓ) := by
  classical
  exact (activeCoordinateSlots A₀ copy .first).biUnion fun a ↦
    ((activeCoordinateSlots B₀ copy .second).filter fun b ↦
      coordinateSlotIndex index a < coordinateSlotIndex index b).image fun b ↦
        AffineForm.add
          (coordinateSlotForm rowU copy index .first a)
          (coordinateSlotForm rowV copy index .second b)

/-- Symbolic first-only affine forms. -/
noncomputable def symbolicFirstOnlyQForms {ℓ : ℕ}
    (rowU : ℕ → ℝ) (A₀ : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ) : Finset (AffineForm ℓ) := by
  classical
  exact (activeCoordinateSlots A₀ copy .first).image fun a ↦
    coordinateSlotForm rowU copy index .first a

/-- Symbolic second-only affine forms. -/
noncomputable def symbolicSecondOnlyQForms {ℓ : ℕ}
    (rowV : ℕ → ℝ) (A₀ B₀ : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ) : Finset (AffineForm ℓ) := by
  classical
  exact ((activeCoordinateSlots B₀ copy .second).filter fun b ↦
    hasZeroBefore (candidateSupport A₀ copy index .first)
      (coordinateSlotIndex index b)).image fun b ↦
        coordinateSlotForm rowV copy index .second b

/-- The complete symbolic affine list for one row and one labelled sparse
parameter pattern. -/
noncomputable def symbolicAffineQForms {ℓ : ℕ}
    (rowU rowV : ℕ → ℝ) (A₀ B₀ : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ) : Finset (AffineForm ℓ) := by
  classical
  exact insert (AffineForm.zero ℓ)
    (symbolicPairedQForms rowU rowV A₀ B₀ copy index ∪
      symbolicFirstOnlyQForms rowU A₀ copy index ∪
      symbolicSecondOnlyQForms rowV A₀ B₀ copy index)

/-- The symbolic paired forms are exactly the paired forms indexed by the
corresponding numerical candidate supports. -/
theorem symbolicPairedQForms_eq_pairedQForms {ℓ : ℕ}
    (rowU rowV : ℕ → ℝ) (A₀ B₀ : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ) :
    symbolicPairedQForms rowU rowV A₀ B₀ copy index =
      pairedQForms
        (labelledCoordinateForm rowU copy index .first)
        (labelledCoordinateForm rowV copy index .second)
        (candidateSupport A₀ copy index .first)
        (candidateSupport B₀ copy index .second) := by
  classical
  ext f
  constructor
  · intro hf
    rw [symbolicPairedQForms] at hf
    rcases Finset.mem_biUnion.mp hf with ⟨a, ha, haf⟩
    rcases Finset.mem_image.mp haf with ⟨b, hb, rfl⟩
    have hai : coordinateSlotIndex index a ∈ candidateSupport A₀ copy index .first := by
      rw [← image_activeCoordinateSlots_eq_candidateSupport A₀ copy index .first]
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have hbi : coordinateSlotIndex index b ∈ candidateSupport B₀ copy index .second := by
      rw [← image_activeCoordinateSlots_eq_candidateSupport B₀ copy index .second]
      exact Finset.mem_image.mpr ⟨b, (Finset.mem_filter.mp hb).1, rfl⟩
    rw [pairedQForms, Finset.mem_biUnion]
    refine ⟨coordinateSlotIndex index a, hai, Finset.mem_image.mpr
      ⟨coordinateSlotIndex index b, Finset.mem_filter.mpr
        ⟨hbi, (Finset.mem_filter.mp hb).2⟩, ?_⟩⟩
    rfl
  · intro hf
    rw [pairedQForms] at hf
    rcases Finset.mem_biUnion.mp hf with ⟨i, hi, hif⟩
    rcases Finset.mem_image.mp hif with ⟨j, hj, rfl⟩
    have hi' : i ∈ (activeCoordinateSlots A₀ copy .first).image
        (coordinateSlotIndex index) := by
      rwa [image_activeCoordinateSlots_eq_candidateSupport]
    rcases Finset.mem_image.mp hi' with ⟨a, ha, hai⟩
    have hj' : j ∈ (activeCoordinateSlots B₀ copy .second).image
        (coordinateSlotIndex index) := by
      rw [image_activeCoordinateSlots_eq_candidateSupport]
      exact (Finset.mem_filter.mp hj).1
    rcases Finset.mem_image.mp hj' with ⟨b, hb, hbj⟩
    rw [symbolicPairedQForms, Finset.mem_biUnion]
    refine ⟨a, ha, Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr
      ⟨hb, ?_⟩, ?_⟩⟩
    · simpa [hai, hbj] using (Finset.mem_filter.mp hj).2
    · simp [coordinateSlotForm, hai, hbj]

/-- The symbolic first-only forms are exactly the first-only forms on the
candidate support. -/
theorem symbolicFirstOnlyQForms_eq_firstOnlyQForms {ℓ : ℕ}
    (rowU : ℕ → ℝ) (A₀ : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ) :
    symbolicFirstOnlyQForms rowU A₀ copy index =
      firstOnlyQForms
        (labelledCoordinateForm rowU copy index .first)
        (candidateSupport A₀ copy index .first) := by
  classical
  rw [symbolicFirstOnlyQForms, firstOnlyQForms,
    ← image_activeCoordinateSlots_eq_candidateSupport A₀ copy index .first,
    Finset.image_image]
  rfl

/-- The symbolic second-only forms are exactly the second-only forms on the
candidate supports. -/
theorem symbolicSecondOnlyQForms_eq_secondOnlyQForms {ℓ : ℕ}
    (rowV : ℕ → ℝ) (A₀ B₀ : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ) :
    symbolicSecondOnlyQForms rowV A₀ B₀ copy index =
      secondOnlyQForms
        (labelledCoordinateForm rowV copy index .second)
        (candidateSupport A₀ copy index .first)
        (candidateSupport B₀ copy index .second) := by
  classical
  ext f
  constructor
  · intro hf
    rw [symbolicSecondOnlyQForms] at hf
    rcases Finset.mem_image.mp hf with ⟨b, hb, rfl⟩
    have hbi : coordinateSlotIndex index b ∈ candidateSupport B₀ copy index .second := by
      rw [← image_activeCoordinateSlots_eq_candidateSupport B₀ copy index .second]
      exact Finset.mem_image.mpr ⟨b, (Finset.mem_filter.mp hb).1, rfl⟩
    rw [secondOnlyQForms, Finset.mem_image]
    exact ⟨coordinateSlotIndex index b, Finset.mem_filter.mpr
      ⟨hbi, (Finset.mem_filter.mp hb).2⟩, rfl⟩
  · intro hf
    rw [secondOnlyQForms] at hf
    rcases Finset.mem_image.mp hf with ⟨j, hj, rfl⟩
    have hj' : j ∈ (activeCoordinateSlots B₀ copy .second).image
        (coordinateSlotIndex index) := by
      rw [image_activeCoordinateSlots_eq_candidateSupport]
      exact (Finset.mem_filter.mp hj).1
    rcases Finset.mem_image.mp hj' with ⟨b, hb, hbj⟩
    rw [symbolicSecondOnlyQForms, Finset.mem_image]
    refine ⟨b, Finset.mem_filter.mpr ⟨hb, ?_⟩, ?_⟩
    · simpa [hbj] using (Finset.mem_filter.mp hj).2
    · simp [coordinateSlotForm, hbj]

/-- The assembled symbolic list is exactly the fixed affine list already
known to compute `q`. -/
theorem symbolicAffineQForms_eq_finiteAffineQForms {ℓ : ℕ}
    (rowU rowV : ℕ → ℝ) (A₀ B₀ : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ) :
    symbolicAffineQForms rowU rowV A₀ B₀ copy index =
      finiteAffineQForms
        (labelledCoordinateForm rowU copy index .first)
        (labelledCoordinateForm rowV copy index .second)
        (candidateSupport A₀ copy index .first)
        (candidateSupport B₀ copy index .second) := by
  rw [symbolicAffineQForms, finiteAffineQForms,
    symbolicPairedQForms_eq_pairedQForms,
    symbolicFirstOnlyQForms_eq_firstOnlyQForms,
    symbolicSecondOnlyQForms_eq_secondOnlyQForms]

/-- Absolute evaluations of the assembled symbolic affine list. -/
noncomputable def symbolicAffineQValues {ℓ : ℕ}
    (rowU rowV : ℕ → ℝ) (A₀ B₀ : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (t : Fin ℓ → ℝ) : Finset ℝ :=
  (symbolicAffineQForms rowU rowV A₀ B₀ copy index).image fun f ↦ |f.eval t|

theorem symbolicAffineQValues_nonempty {ℓ : ℕ}
    (rowU rowV : ℕ → ℝ) (A₀ B₀ : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (t : Fin ℓ → ℝ) :
    (symbolicAffineQValues rowU rowV A₀ B₀ copy index t).Nonempty := by
  refine ⟨0, ?_⟩
  simp [symbolicAffineQValues, symbolicAffineQForms]

/-- Symbolic evaluation agrees with evaluation of the numerical fixed list. -/
theorem symbolicAffineQValues_eq_finiteAffineQValues {ℓ : ℕ}
    (rowU rowV : ℕ → ℝ) (A₀ B₀ : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (t : Fin ℓ → ℝ) :
    symbolicAffineQValues rowU rowV A₀ B₀ copy index t =
      finiteAffineQValues
        (labelledCoordinateForm rowU copy index .first)
        (labelledCoordinateForm rowV copy index .second)
        (candidateSupport A₀ copy index .first)
        (candidateSupport B₀ copy index .second) t := by
  rw [symbolicAffineQValues, finiteAffineQValues_eq_image,
    symbolicAffineQForms_eq_finiteAffineQForms]

/-- The paired part of the symbolic list is invariant inside a sparse type. -/
theorem symbolicPairedQForms_eq_of_sparseOrderType_eq
    {D A₀ B₀ : Finset ℕ} {ℓ : ℕ} (rowU rowV : ℕ → ℝ)
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index')
    (hAD : A₀ ⊆ D) (hBD : B₀ ⊆ D)
    (hrowU : ∀ n, n ∉ A₀ → rowU n = 0)
    (hrowV : ∀ n, n ∉ B₀ → rowV n = 0) :
    symbolicPairedQForms rowU rowV A₀ B₀ copy index =
      symbolicPairedQForms rowU rowV A₀ B₀ copy' index' := by
  classical
  rw [symbolicPairedQForms, symbolicPairedQForms,
    activeCoordinateSlots_eq_of_sparseOrderType_eq h .first]
  apply Finset.biUnion_congr rfl
  intro a ha
  rw [activeCoordinateSlots_eq_of_sparseOrderType_eq h .second]
  have hfilter :
      (activeCoordinateSlots B₀ copy' .second).filter
          (fun b ↦ coordinateSlotIndex index a < coordinateSlotIndex index b) =
        (activeCoordinateSlots B₀ copy' .second).filter
          (fun b ↦ coordinateSlotIndex index' a < coordinateSlotIndex index' b) := by
    apply Finset.filter_congr
    intro b hb
    exact coordinateSlotIndex_lt_iff_of_sparseOrderType_eq h hAD hBD a b
  rw [hfilter]
  apply Finset.image_congr
  intro b hb
  change AffineForm.add
      (coordinateSlotForm rowU copy index .first a)
      (coordinateSlotForm rowV copy index .second b) =
    AffineForm.add
      (coordinateSlotForm rowU copy' index' .first a)
      (coordinateSlotForm rowV copy' index' .second b)
  congr 1
  · exact coordinateSlotForm_eq_of_sparseOrderType_eq rowU h hAD hrowU .first a
  exact coordinateSlotForm_eq_of_sparseOrderType_eq rowV h hBD hrowV .second b

/-- The first-only part of the symbolic list is invariant inside a sparse type. -/
theorem symbolicFirstOnlyQForms_eq_of_sparseOrderType_eq
    {D A₀ : Finset ℕ} {ℓ : ℕ} (rowU : ℕ → ℝ)
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index')
    (hAD : A₀ ⊆ D) (hrowU : ∀ n, n ∉ A₀ → rowU n = 0) :
    symbolicFirstOnlyQForms rowU A₀ copy index =
      symbolicFirstOnlyQForms rowU A₀ copy' index' := by
  classical
  rw [symbolicFirstOnlyQForms, symbolicFirstOnlyQForms,
    activeCoordinateSlots_eq_of_sparseOrderType_eq h .first]
  apply Finset.image_congr
  intro a ha
  exact coordinateSlotForm_eq_of_sparseOrderType_eq rowU h hAD hrowU .first a

/-- The second-only part of the symbolic list is invariant inside a sparse type. -/
theorem symbolicSecondOnlyQForms_eq_of_sparseOrderType_eq
    {D A₀ B₀ : Finset ℕ} {ℓ s : ℕ} (rowV : ℕ → ℝ)
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index')
    (hBD : B₀ ⊆ D) (hrowV : ∀ n, n ∉ B₀ → rowV n = 0)
    (hsize : A₀.card + ℓ ≤ s) (hprotected : Finset.range (s + 1) ⊆ D) :
    symbolicSecondOnlyQForms rowV A₀ B₀ copy index =
      symbolicSecondOnlyQForms rowV A₀ B₀ copy' index' := by
  classical
  rw [symbolicSecondOnlyQForms, symbolicSecondOnlyQForms,
    activeCoordinateSlots_eq_of_sparseOrderType_eq h .second]
  have hfilter :
      (activeCoordinateSlots B₀ copy' .second).filter
          (fun b ↦ hasZeroBefore (candidateSupport A₀ copy index .first)
            (coordinateSlotIndex index b)) =
        (activeCoordinateSlots B₀ copy' .second).filter
          (fun b ↦ hasZeroBefore (candidateSupport A₀ copy' index' .first)
            (coordinateSlotIndex index' b)) := by
    apply Finset.filter_congr
    intro b hb
    exact coordinateSlot_hasZeroBefore_iff_of_sparseOrderType_eq
      h hsize hprotected b
  rw [hfilter]
  apply Finset.image_congr
  intro b hb
  exact coordinateSlotForm_eq_of_sparseOrderType_eq rowV h hBD hrowV .second b

/-- The full symbolic affine list is identical for every realization of one
sparse order type. -/
theorem symbolicAffineQForms_eq_of_sparseOrderType_eq
    {D A₀ B₀ : Finset ℕ} {ℓ s : ℕ} (rowU rowV : ℕ → ℝ)
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index')
    (hAD : A₀ ⊆ D) (hBD : B₀ ⊆ D)
    (hrowU : ∀ n, n ∉ A₀ → rowU n = 0)
    (hrowV : ∀ n, n ∉ B₀ → rowV n = 0)
    (hsize : A₀.card + ℓ ≤ s) (hprotected : Finset.range (s + 1) ⊆ D) :
    symbolicAffineQForms rowU rowV A₀ B₀ copy index =
      symbolicAffineQForms rowU rowV A₀ B₀ copy' index' := by
  rw [symbolicAffineQForms, symbolicAffineQForms,
    symbolicPairedQForms_eq_of_sparseOrderType_eq rowU rowV h hAD hBD hrowU hrowV,
    symbolicFirstOnlyQForms_eq_of_sparseOrderType_eq rowU h hAD hrowU,
    symbolicSecondOnlyQForms_eq_of_sparseOrderType_eq rowV h hBD hrowV hsize hprotected]

/-- Consequently, absolute evaluation of the symbolic list is also invariant
inside a sparse order type. -/
theorem symbolicAffineQValues_eq_of_sparseOrderType_eq
    {D A₀ B₀ : Finset ℕ} {ℓ s : ℕ} (rowU rowV : ℕ → ℝ)
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index')
    (hAD : A₀ ⊆ D) (hBD : B₀ ⊆ D)
    (hrowU : ∀ n, n ∉ A₀ → rowU n = 0)
    (hrowV : ∀ n, n ∉ B₀ → rowV n = 0)
    (hsize : A₀.card + ℓ ≤ s) (hprotected : Finset.range (s + 1) ⊆ D)
    (t : Fin ℓ → ℝ) :
    symbolicAffineQValues rowU rowV A₀ B₀ copy index t =
      symbolicAffineQValues rowU rowV A₀ B₀ copy' index' t := by
  rw [symbolicAffineQValues, symbolicAffineQValues,
    symbolicAffineQForms_eq_of_sparseOrderType_eq rowU rowV h hAD hBD hrowU hrowV
      hsize hprotected]

/-- Uniform bound for the number of symbolic affine entries. -/
theorem card_symbolicAffineQForms_le {ℓ : ℕ}
    (rowU rowV : ℕ → ℝ) (A₀ B₀ : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ) :
    (symbolicAffineQForms rowU rowV A₀ B₀ copy index).card ≤
      1 + (A₀.card + ℓ) * (B₀.card + ℓ) + (A₀.card + ℓ) + (B₀.card + ℓ) := by
  rw [symbolicAffineQForms_eq_finiteAffineQForms]
  have hforms := card_finiteAffineQForms_le
    (labelledCoordinateForm rowU copy index .first)
    (labelledCoordinateForm rowV copy index .second)
    (candidateSupport A₀ copy index .first)
    (candidateSupport B₀ copy index .second)
  have hA := card_candidateSupport_le A₀ copy index .first
  have hB := card_candidateSupport_le B₀ copy index .second
  have hmul := Nat.mul_le_mul hA hB
  omega

/-- For a fixed row and labelled sparse parameter, `q` is the maximum of the
absolute evaluations of the symbolic affine list. -/
theorem qSeminorm_eq_max_symbolicAffineQValues {ℓ : ℕ}
    (rowU rowV u v : RealL2) (A₀ B₀ : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (t : Fin ℓ → ℝ)
    (hrowU : ∀ n, n ∉ A₀ → rowU n = 0)
    (hrowV : ∀ n, n ∉ B₀ → rowV n = 0)
    (hu : ∀ n, u n =
      (labelledCoordinateForm (fun i ↦ rowU i) copy index .first n).eval t)
    (hv : ∀ n, v n =
      (labelledCoordinateForm (fun i ↦ rowV i) copy index .second n).eval t) :
    qSeminorm (WithLp.toLp 2 (u, v)) =
      (symbolicAffineQValues (fun i ↦ rowU i) (fun i ↦ rowV i)
        A₀ B₀ copy index t).max'
      (symbolicAffineQValues_nonempty (fun i ↦ rowU i) (fun i ↦ rowV i)
        A₀ B₀ copy index t) := by
  have hq := qSeminorm_eq_max_labelledAffineQValues rowU rowV u v A₀ B₀
    copy index t hrowU hrowV hu hv
  have hvalues := symbolicAffineQValues_eq_finiteAffineQValues
    (fun i ↦ rowU i) (fun i ↦ rowV i) A₀ B₀ copy index t
  calc
    qSeminorm (WithLp.toLp 2 (u, v)) =
        (finiteAffineQValues
          (labelledCoordinateForm (fun i ↦ rowU i) copy index .first)
          (labelledCoordinateForm (fun i ↦ rowV i) copy index .second)
          (candidateSupport A₀ copy index .first)
          (candidateSupport B₀ copy index .second) t).max'
        (finiteAffineQValues_nonempty
          (labelledCoordinateForm (fun i ↦ rowU i) copy index .first)
          (labelledCoordinateForm (fun i ↦ rowV i) copy index .second)
          (candidateSupport A₀ copy index .first)
          (candidateSupport B₀ copy index .second) t) := hq
    _ = (symbolicAffineQValues (fun i ↦ rowU i) (fun i ↦ rowV i)
        A₀ B₀ copy index t).max'
        (symbolicAffineQValues_nonempty (fun i ↦ rowU i) (fun i ↦ rowV i)
          A₀ B₀ copy index t) := by
      apply le_antisymm
      · rw [Finset.max'_le_iff]
        intro c hc
        apply Finset.le_max'
        rwa [hvalues]
      · rw [Finset.max'_le_iff]
        intro c hc
        apply Finset.le_max'
        rwa [← hvalues]

end NormFormula.HalfGraph
