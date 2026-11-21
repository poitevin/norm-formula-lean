import NormFormula.Combinatorics.AffineQList

/-!
# Transport within a sparse order type

Equal sparse order codes preserve not only the evident order relations, but
also the less immediate question whether a second-copy position has an earlier
zero first-copy position.  The protected initial block is what makes the latter
predicate discrete: beyond the block a counting argument forces a zero, while
inside the block every position is protected and its occupancy is preserved.
-/

namespace NormFormula.HalfGraph

@[simp]
theorem natOrderRelation_eq_lt_iff (i j : ℕ) :
    natOrderRelation i j = .lt ↔ i < j := by
  by_cases hij : i < j
  · simp [natOrderRelation, hij]
  · by_cases hieq : i = j
    · simp [natOrderRelation, hieq]
    · simp [natOrderRelation, hij, hieq]

@[simp]
theorem natOrderRelation_eq_eq_iff (i j : ℕ) :
    natOrderRelation i j = .eq ↔ i = j := by
  by_cases hij : i < j
  · have hne : i ≠ j := ne_of_lt hij
    simp [natOrderRelation, hij, hne]
  · by_cases hieq : i = j
    · simp [natOrderRelation, hieq]
    · simp [natOrderRelation, hij, hieq]

/-- Equality of order-relation codes preserves strict order. -/
theorem natOrderRelation_eq_preserves_lt {i j i' j' : ℕ}
    (h : natOrderRelation i j = natOrderRelation i' j') :
    (i < j ↔ i' < j') := by
  rw [← natOrderRelation_eq_lt_iff i j,
    ← natOrderRelation_eq_lt_iff i' j', h]

/-- Equality of order-relation codes preserves equality. -/
theorem natOrderRelation_eq_preserves_eq {i j i' j' : ℕ}
    (h : natOrderRelation i j = natOrderRelation i' j') :
    (i = j ↔ i' = j') := by
  rw [← natOrderRelation_eq_eq_iff i j,
    ← natOrderRelation_eq_eq_iff i' j', h]

/-- Equal sparse types preserve strict order between any two labels. -/
theorem sparseOrderType_eq_preserves_pair_lt {D : Finset ℕ} {ℓ : ℕ}
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index')
    (a b : Fin ℓ) :
    (index a < index b ↔ index' a < index' b) := by
  exact natOrderRelation_eq_preserves_lt
    (sparseOrderType_eq_preserves_pair_relation h a b)

/-- Equal sparse types preserve equality between any two labels. -/
theorem sparseOrderType_eq_preserves_pair_eq {D : Finset ℕ} {ℓ : ℕ}
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index')
    (a b : Fin ℓ) :
    (index a = index b ↔ index' a = index' b) := by
  exact natOrderRelation_eq_preserves_eq
    (sparseOrderType_eq_preserves_pair_relation h a b)

/-- At a protected numerical position, equal sparse types preserve membership
in a candidate support. -/
theorem candidateSupport_mem_iff_of_sparseOrderType_eq
    {D rowSupport : Finset ℕ} {ℓ : ℕ}
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index')
    (target : CoordinateCopy) {d : ℕ} (hd : d ∈ D) :
    d ∈ candidateSupport rowSupport copy index target ↔
      d ∈ candidateSupport rowSupport copy' index' target := by
  constructor
  · intro hmem
    rw [candidateSupport, Finset.mem_union] at hmem ⊢
    rcases hmem with hrow | hlabel
    · exact Or.inl hrow
    · right
      rw [labelIndexSet, Finset.mem_image] at hlabel ⊢
      rcases hlabel with ⟨a, ha, hai⟩
      refine ⟨a, ?_, ?_⟩
      · rw [Finset.mem_filter] at ha ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        calc
          copy' a = copy a := (sparseOrderType_eq_preserves_copy h a).symm
          _ = target := ha.2
      · exact (sparseOrderType_eq_preserves_protected_relations h a hd).2.1.mp hai
  · intro hmem
    rw [candidateSupport, Finset.mem_union] at hmem ⊢
    rcases hmem with hrow | hlabel
    · exact Or.inl hrow
    · right
      rw [labelIndexSet, Finset.mem_image] at hlabel ⊢
      rcases hlabel with ⟨a, ha, hai⟩
      refine ⟨a, ?_, ?_⟩
      · rw [Finset.mem_filter] at ha ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        calc
          copy a = copy' a := sparseOrderType_eq_preserves_copy h a
          _ = target := ha.2
      · exact (sparseOrderType_eq_preserves_protected_relations h a hd).2.1.mpr hai

/-- At a protected position, the coordinate affine form itself is unchanged
when the sparse realization changes within its type. -/
theorem labelledCoordinateForm_eq_at_protected
    {D : Finset ℕ} {ℓ : ℕ} (row : ℕ → ℝ)
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index')
    (target : CoordinateCopy) {d : ℕ} (hd : d ∈ D) :
    labelledCoordinateForm row copy index target d =
      labelledCoordinateForm row copy' index' target d := by
  apply AffineForm.ext
  · rfl
  · intro a
    have hcopy : copy a = target ↔ copy' a = target := by
      rw [sparseOrderType_eq_preserves_copy h a]
    have hindex : index a = d ↔ index' a = d :=
      (sparseOrderType_eq_preserves_protected_relations h a hd).2.1
    simp only [labelledCoordinateForm]
    have hp : (copy a = target ∧ index a = d) ↔
        (copy' a = target ∧ index' a = d) := and_congr hcopy hindex
    by_cases ha : copy a = target ∧ index a = d
    · simp [ha, hp.mp ha]
    · have ha' : ¬(copy' a = target ∧ index' a = d) := fun ha' ↦ ha (hp.mpr ha')
      simp [ha, ha']

/-- At the position carried by a label, the coordinate affine form is also
unchanged. Row constants agree because row support positions are protected;
all coefficients agree by pairwise equality preservation. -/
theorem labelledCoordinateForm_eq_at_label
    {D rowSupport : Finset ℕ} {ℓ : ℕ} (row : ℕ → ℝ)
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index')
    (hrowD : rowSupport ⊆ D) (hrow : ∀ n, n ∉ rowSupport → row n = 0)
    (target : CoordinateCopy) (b : Fin ℓ) :
    labelledCoordinateForm row copy index target (index b) =
      labelledCoordinateForm row copy' index' target (index' b) := by
  apply AffineForm.ext
  · by_cases hb : index b ∈ rowSupport
    · have hbD : index b ∈ D := hrowD hb
      have hindex : index' b = index b := by
        exact (sparseOrderType_eq_preserves_protected_relations h b hbD).2.1.mp rfl
      simp [labelledCoordinateForm, hindex]
    · have hb' : index' b ∉ rowSupport := by
        intro hb'
        have hb'D : index' b ∈ D := hrowD hb'
        have hindex : index b = index' b :=
          (sparseOrderType_eq_preserves_protected_relations h b hb'D).2.1.mpr rfl
        exact hb (hindex ▸ hb')
      simp [labelledCoordinateForm, hrow _ hb, hrow _ hb']
  · intro a
    have hcopy : copy a = target ↔ copy' a = target := by
      rw [sparseOrderType_eq_preserves_copy h a]
    have hindex : index a = index b ↔ index' a = index' b :=
      sparseOrderType_eq_preserves_pair_eq h a b
    simp only [labelledCoordinateForm]
    have hp : (copy a = target ∧ index a = index b) ↔
        (copy' a = target ∧ index' a = index' b) := and_congr hcopy hindex
    by_cases ha : copy a = target ∧ index a = index b
    · simp [ha, hp.mp ha]
    · have ha' : ¬(copy' a = target ∧ index' a = index' b) :=
        fun ha' ↦ ha (hp.mpr ha')
      simp [ha, ha']

/-- If a finite set has fewer than `b` elements, some position below `b`
lies outside it. -/
theorem hasZeroBefore_of_card_lt (A : Finset ℕ) {b : ℕ} (hcard : A.card < b) :
    hasZeroBefore A b := by
  by_contra hzero
  have hsubset : Finset.range b ⊆ A := by
    intro a ha
    by_contra haA
    exact hzero ⟨a, Finset.mem_range.mp ha, haA⟩
  have hle := Finset.card_le_card hsubset
  simp at hle
  omega

/-- The predicate `hasZeroBefore` depends only on membership below the given
position. -/
theorem hasZeroBefore_congr_of_prefix {A A' : Finset ℕ} {b : ℕ}
    (hmem : ∀ a, a < b → (a ∈ A ↔ a ∈ A')) :
    hasZeroBefore A b ↔ hasZeroBefore A' b := by
  constructor
  · rintro ⟨a, hab, ha⟩
    exact ⟨a, hab, fun ha' ↦ ha ((hmem a hab).mpr ha')⟩
  · rintro ⟨a, hab, ha⟩
    exact ⟨a, hab, fun ha' ↦ ha ((hmem a hab).mp ha')⟩

/-- For a fixed numerical second-copy position, equal sparse types preserve
the existence of an earlier zero. The initial block through `s` is assumed
protected, and `s` bounds the candidate first support size. -/
theorem hasZeroBefore_candidateSupport_fixed_iff
    {D rowSupport : Finset ℕ} {ℓ s : ℕ}
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index')
    (hsize : rowSupport.card + ℓ ≤ s)
    (hprotected : Finset.range (s + 1) ⊆ D) (b : ℕ) :
    hasZeroBefore (candidateSupport rowSupport copy index .first) b ↔
      hasZeroBefore (candidateSupport rowSupport copy' index' .first) b := by
  by_cases hb : b ≤ s
  · apply hasZeroBefore_congr_of_prefix
    intro a hab
    apply candidateSupport_mem_iff_of_sparseOrderType_eq h
    apply hprotected
    rw [Finset.mem_range]
    omega
  · have hA : (candidateSupport rowSupport copy index .first).card < b :=
      (card_candidateSupport_le rowSupport copy index .first).trans_lt
        (lt_of_le_of_lt hsize (by omega))
    have hA' : (candidateSupport rowSupport copy' index' .first).card < b :=
      (card_candidateSupport_le rowSupport copy' index' .first).trans_lt
        (lt_of_le_of_lt hsize (by omega))
    exact iff_of_true (hasZeroBefore_of_card_lt _ hA)
      (hasZeroBefore_of_card_lt _ hA')

/-- The subtle second-only predicate is invariant for corresponding labelled
positions in equal sparse types. This is the protected-prefix step used in
the manuscript's cancellation-invariant affine-list argument. -/
theorem hasZeroBefore_candidateSupport_label_iff
    {D rowSupport : Finset ℕ} {ℓ s : ℕ}
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index')
    (hsize : rowSupport.card + ℓ ≤ s)
    (hprotected : Finset.range (s + 1) ⊆ D) (b : Fin ℓ) :
    hasZeroBefore (candidateSupport rowSupport copy index .first) (index b) ↔
      hasZeroBefore (candidateSupport rowSupport copy' index' .first) (index' b) := by
  by_cases hb : index b ≤ s
  · have hibD : index b ∈ D := by
      apply hprotected
      rw [Finset.mem_range]
      omega
    have hindex : index' b = index b :=
      (sparseOrderType_eq_preserves_protected_relations h b hibD).2.1.mp rfl
    rw [hindex]
    exact hasZeroBefore_candidateSupport_fixed_iff h hsize hprotected (index b)
  · have hsD : s ∈ D := by
      apply hprotected
      rw [Finset.mem_range]
      omega
    have hb' : s < index' b :=
      (sparseOrderType_eq_preserves_protected_relations h b hsD).2.2.mp (by omega)
    have hA : (candidateSupport rowSupport copy index .first).card < index b :=
      (card_candidateSupport_le rowSupport copy index .first).trans_lt
        (lt_of_le_of_lt hsize (by omega))
    have hA' : (candidateSupport rowSupport copy' index' .first).card < index' b :=
      (card_candidateSupport_le rowSupport copy' index' .first).trans_lt
        (lt_of_le_of_lt hsize hb')
    exact iff_of_true (hasZeroBefore_of_card_lt _ hA)
      (hasZeroBefore_of_card_lt _ hA')

end NormFormula.HalfGraph
