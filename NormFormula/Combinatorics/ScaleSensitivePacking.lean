import NormFormula.Combinatorics.ScaleSensitiveDiscretization
import NormFormula.Combinatorics.StrongPairPacking

/-!
# Scale-sensitive real packing

This file connects real sup-separated evaluation families to the finite-range
strong-pair packing theorem. It packages downward discretization as a finite
function class, preserves cardinality and two-level separation, and transfers
a finite fat-shattering dimension bound to the required discrete strong-
shattering dimension bound.
-/

namespace NormFormula

/-- A localized strong-shattering witness becomes a whole-type witness after
restricting the row type to the selected finite set. -/
theorem StronglyShattersAtUnit.to_isStronglyShatteredAtUnit_subtype
    {Row Parameter : Type*} [DecidableEq Row]
    {value : Row → Parameter → ℕ} {rows : Finset Row}
    {threshold : Row → ℕ}
    (hshatters : StronglyShattersAtUnit value rows threshold) :
    IsStronglyShatteredAtUnit
      (fun row : ↥rows ↦ fun parameter ↦ value row.1 parameter) := by
  classical
  refine ⟨fun row ↦ threshold row.1, ?_⟩
  intro S
  let liftedRows : Finset Row := S.image Subtype.val
  have hliftedSubset : liftedRows ⊆ rows := by
    intro row hrow
    obtain ⟨selectedRow, _, rfl⟩ := Finset.mem_image.mp hrow
    exact selectedRow.2
  obtain ⟨parameter, hhigh, hlow⟩ :=
    hshatters liftedRows hliftedSubset
  refine ⟨parameter, ?_, ?_⟩
  · intro row hrow
    apply hhigh row.1
    exact Finset.mem_image.mpr ⟨row, hrow, rfl⟩
  · intro row hrow
    apply hlow row.1 row.2
    intro hrowLifted
    obtain ⟨selectedRow, hselectedRow, heq⟩ :=
      Finset.mem_image.mp hrowLifted
    have hselectedEq : selectedRow = row := Subtype.ext heq
    exact hrow (hselectedEq ▸ hselectedRow)

/-- Downward-discretize every function in a finite real-valued family. -/
noncomputable def floorDiscretizedFamily
    {Row : Type*} [Fintype Row]
    (mesh : ℝ) (family : Finset (Row → ℝ)) :
    Finset (Row → ℕ) := by
  classical
  exact family.image fun f row ↦ floorDiscretization mesh (f row)

@[simp] theorem mem_floorDiscretizedFamily
    {Row : Type*} [Fintype Row]
    {mesh : ℝ} {family : Finset (Row → ℝ)} {g : Row → ℕ} :
    g ∈ floorDiscretizedFamily mesh family ↔
      ∃ f ∈ family, (fun row ↦ floorDiscretization mesh (f row)) = g := by
  classical
  simp [floorDiscretizedFamily]

/-- Real separation by two mesh widths on active rows makes discretization
injective on the finite family. -/
theorem card_floorDiscretizedFamily_eq
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {mesh : ℝ} {family : Finset (Row → ℝ)}
    {activeRows : Finset Row}
    (hmesh : 0 < mesh)
    (hnonnegative : ∀ f ∈ family, ∀ row ∈ activeRows, 0 ≤ f row)
    (hseparated : ∀ f ∈ family, ∀ g ∈ family, f ≠ g →
      ∃ row ∈ activeRows, 2 * mesh ≤ |f row - g row|) :
    (floorDiscretizedFamily mesh family).card = family.card := by
  classical
  rw [floorDiscretizedFamily, Finset.card_image_iff]
  intro f hf g hg hfg
  by_contra hne
  obtain ⟨row, hrowActive, hrow⟩ := hseparated f hf g hg hne
  have hdiscrete :
      floorDiscretization mesh (f row) + 2 ≤
          floorDiscretization mesh (g row) ∨
        floorDiscretization mesh (g row) + 2 ≤
          floorDiscretization mesh (f row) := by
    rcases le_abs.mp hrow with hrow | hrow
    · right
      apply floorDiscretization_add_two_le_of_add_two_mul_le
        hmesh (hnonnegative g hg row hrowActive)
      linarith
    · left
      apply floorDiscretization_add_two_le_of_add_two_mul_le
        hmesh (hnonnegative f hf row hrowActive)
      linarith
  have hvalues : floorDiscretization mesh (f row) =
      floorDiscretization mesh (g row) := by
    simpa only using congrFun hfg row
  omega

/-- The discretized family is pairwise two-separated on the active rows. -/
theorem floorDiscretizedFamily_pairwiseTwoSeparatedOn
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {mesh : ℝ} {family : Finset (Row → ℝ)}
    {activeRows : Finset Row}
    (hmesh : 0 < mesh)
    (hnonnegative : ∀ f ∈ family, ∀ row ∈ activeRows, 0 ≤ f row)
    (hseparated : ∀ f ∈ family, ∀ g ∈ family, f ≠ g →
      ∃ row ∈ activeRows, 2 * mesh ≤ |f row - g row|) :
    IsPairwiseTwoSeparatedOn
      (floorDiscretizedFamily mesh family) activeRows := by
  classical
  intro discreteF hdiscreteF discreteG hdiscreteG hfg
  obtain ⟨f, hf, rfl⟩ := mem_floorDiscretizedFamily.mp hdiscreteF
  obtain ⟨g, hg, rfl⟩ := mem_floorDiscretizedFamily.mp hdiscreteG
  have hfgReal : f ≠ g := by
    intro hfgReal
    subst g
    exact hfg rfl
  obtain ⟨row, hrowActive, hrow⟩ :=
    hseparated f hf g hg hfgReal
  refine ⟨row, hrowActive, ?_⟩
  rcases le_abs.mp hrow with hrow | hrow
  · right
    apply floorDiscretization_add_two_le_of_add_two_mul_le
      hmesh (hnonnegative g hg row hrowActive)
    linarith
  · left
    apply floorDiscretization_add_two_le_of_add_two_mul_le
      hmesh (hnonnegative f hf row hrowActive)
    linarith

/-- A real upper bound on active rows gives the successor finite-range bound
required by the natural-valued packing theorem. -/
theorem floorDiscretizedFamily_boundedOn
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {mesh upperBound : ℝ} {family : Finset (Row → ℝ)}
    {activeRows : Finset Row}
    (hmesh : 0 < mesh)
    (hupper : ∀ f ∈ family, ∀ row ∈ activeRows, f row ≤ upperBound) :
    ∀ g ∈ floorDiscretizedFamily mesh family, ∀ row ∈ activeRows,
      g row < floorDiscretization mesh upperBound + 1 := by
  classical
  intro g hg row hrow
  obtain ⟨f, hf, rfl⟩ := mem_floorDiscretizedFamily.mp hg
  have hle := floorDiscretization_le_of_le hmesh
    (hupper f hf row hrow)
  change floorDiscretization mesh (f row) <
    floorDiscretization mesh upperBound + 1
  exact Nat.lt_succ_of_le hle

/-- Fat-shattering dimension at a fixed positive margin, localized to an
active finite row set. -/
def HasFatShatteringDimensionAtMostOn
    {Row : Type*} [DecidableEq Row]
    (family : Finset (Row → ℝ)) (activeRows : Finset Row)
    (margin : ℝ) (dimension : ℕ) : Prop :=
  ∀ rows : Finset Row, rows ⊆ activeRows →
    IsFatShattered
      (fun row : ↥rows ↦ fun f : ↥family ↦ f.1 row.1) margin →
      rows.card ≤ dimension

/-- Translate every function in a finite real-valued family by a common
offset. -/
noncomputable def translatedRealFamily
    {Row : Type*} [Fintype Row]
    (offset : ℝ) (family : Finset (Row → ℝ)) : Finset (Row → ℝ) := by
  classical
  exact family.image fun f row ↦ f row + offset

@[simp] theorem mem_translatedRealFamily
    {Row : Type*} [Fintype Row]
    {offset : ℝ} {family : Finset (Row → ℝ)} {g : Row → ℝ} :
    g ∈ translatedRealFamily offset family ↔
      ∃ f ∈ family, (fun row ↦ f row + offset) = g := by
  classical
  simp [translatedRealFamily]

/-- Common translation is injective on a finite function family. -/
theorem card_translatedRealFamily
    {Row : Type*} [Fintype Row]
    (offset : ℝ) (family : Finset (Row → ℝ)) :
    (translatedRealFamily offset family).card = family.card := by
  classical
  rw [translatedRealFamily, Finset.card_image_iff]
  intro f _ g _ hfg
  funext row
  have hrow := congrFun hfg row
  linarith

/-- Pairwise sup separation is unchanged by common translation. -/
theorem translatedRealFamily_separated
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {offset separation : ℝ} {family : Finset (Row → ℝ)}
    {activeRows : Finset Row}
    (hseparated : ∀ f ∈ family, ∀ g ∈ family, f ≠ g →
      ∃ row ∈ activeRows, separation ≤ |f row - g row|) :
    ∀ f ∈ translatedRealFamily offset family,
      ∀ g ∈ translatedRealFamily offset family, f ≠ g →
        ∃ row ∈ activeRows, separation ≤ |f row - g row| := by
  classical
  intro translatedF htranslatedF translatedG htranslatedG hfg
  obtain ⟨f, hf, rfl⟩ := mem_translatedRealFamily.mp htranslatedF
  obtain ⟨g, hg, rfl⟩ := mem_translatedRealFamily.mp htranslatedG
  have hfgOriginal : f ≠ g := by
    intro hfgOriginal
    subst g
    exact hfg rfl
  obtain ⟨row, hrow, hgap⟩ :=
    hseparated f hf g hg hfgOriginal
  refine ⟨row, hrow, ?_⟩
  simpa only [add_sub_add_right_eq_sub] using hgap

/-- A fat-dimension bound is invariant under common translation of a finite
function family. -/
theorem translatedRealFamily_hasFatShatteringDimensionAtMostOn
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {offset margin : ℝ} {family : Finset (Row → ℝ)}
    {activeRows : Finset Row} {dimension : ℕ}
    (hfat : HasFatShatteringDimensionAtMostOn
      family activeRows margin dimension) :
    HasFatShatteringDimensionAtMostOn
      (translatedRealFamily offset family) activeRows margin dimension := by
  classical
  intro rows hrows htranslatedFat
  have hpreimage : ∀ translatedFunction :
      ↥(translatedRealFamily offset family),
      ∃ originalFunction : ↥family, ∀ row,
        originalFunction.1 row + offset = translatedFunction.1 row := by
    intro translatedFunction
    obtain ⟨originalFunction, horiginalMem, heq⟩ :=
      mem_translatedRealFamily.mp translatedFunction.2
    refine ⟨⟨originalFunction, horiginalMem⟩, ?_⟩
    intro row
    exact congrFun heq row
  choose preimage hpreimageValue using hpreimage
  apply hfat rows hrows
  have htranslatedOriginal : IsFatShattered
      (fun row : ↥rows ↦ fun originalFunction : ↥family ↦
        originalFunction.1 row.1 + offset) margin := by
    apply htranslatedFat.reparam preimage
    intro row translatedFunction
    exact hpreimageValue translatedFunction row.1
  exact htranslatedOriginal.of_add_const

/-- A fat-shattering dimension bound at half the mesh transfers to a strong-
shattering dimension bound for the discretized finite family. -/
theorem floorDiscretizedFamily_hasStrongShatteringDimensionAtMostOn
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {mesh : ℝ} {family : Finset (Row → ℝ)}
    {activeRows : Finset Row} {dimension : ℕ}
    (hmesh : 0 < mesh)
    (hnonnegative : ∀ f ∈ family, ∀ row ∈ activeRows, 0 ≤ f row)
    (hfat : HasFatShatteringDimensionAtMostOn
      family activeRows (mesh / 2) dimension) :
    HasStrongShatteringDimensionAtMostOn
      (floorDiscretizedFamily mesh family) activeRows dimension := by
  classical
  intro rows hrows threshold hstrong
  apply hfat rows hrows
  have hpreimage : ∀ discreteFunction :
      ↥(floorDiscretizedFamily mesh family),
      ∃ originalFunction : ↥family, ∀ row,
        floorDiscretization mesh (originalFunction.1 row) =
          discreteFunction.1 row := by
    intro discreteFunction
    obtain ⟨originalFunction, horiginalMem, heq⟩ :=
      mem_floorDiscretizedFamily.mp discreteFunction.2
    refine ⟨⟨originalFunction, horiginalMem⟩, ?_⟩
    intro row
    exact congrFun heq row
  choose preimage hpreimageValue using hpreimage
  have hstrongOriginal : StronglyShattersAtUnit
      (fun row (originalFunction : ↥family) ↦
        floorDiscretization mesh (originalFunction.1 row))
      rows threshold := by
    apply hstrong.reparam preimage
    intro row discreteFunction
    exact hpreimageValue discreteFunction row
  apply isFatShattered_half_mesh_of_stronglyShattered_discretization
    hmesh
  · intro row originalFunction
    exact hnonnegative originalFunction.1 originalFunction.2 row.1
      (hrows row.2)
  · exact hstrongOriginal.to_isStronglyShatteredAtUnit_subtype

/-- Real scale-sensitive packing, obtained in one step from the finite-range
packing theorem after downward discretization. -/
theorem card_lt_strongPairIterationFamilySize_of_real_separated
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {mesh upperBound : ℝ} {family : Finset (Row → ℝ)}
    {activeRows : Finset Row} {dimension steps : ℕ}
    (hmesh : 0 < mesh) (hsteps : steps ≤ activeRows.card)
    (hcount : strongShatteringPairBound (Fintype.card Row)
      (floorDiscretization mesh upperBound + 1) dimension < 2 ^ steps)
    (hnonnegative : ∀ f ∈ family, ∀ row ∈ activeRows, 0 ≤ f row)
    (hupper : ∀ f ∈ family, ∀ row ∈ activeRows, f row ≤ upperBound)
    (hseparated : ∀ f ∈ family, ∀ g ∈ family, f ≠ g →
      ∃ row ∈ activeRows, 2 * mesh ≤ |f row - g row|)
    (hfat : HasFatShatteringDimensionAtMostOn
      family activeRows (mesh / 2) dimension) :
    family.card < strongPairIterationFamilySize activeRows.card
      (floorDiscretization mesh upperBound + 1) steps := by
  let discreteFamily := floorDiscretizedFamily mesh family
  have hpacking := card_lt_strongPairIterationFamilySize
    (family := discreteFamily) (activeRows := activeRows)
    (dimension := dimension) (steps := steps)
    (by omega : 0 < floorDiscretization mesh upperBound + 1)
    hsteps hcount
    (floorDiscretizedFamily_pairwiseTwoSeparatedOn
      hmesh hnonnegative hseparated)
    (floorDiscretizedFamily_boundedOn hmesh hupper)
    (floorDiscretizedFamily_hasStrongShatteringDimensionAtMostOn
      hmesh hnonnegative hfat)
  rw [card_floorDiscretizedFamily_eq hmesh hnonnegative hseparated] at hpacking
  exact hpacking

/-- Scale-sensitive packing for a real family bounded in an arbitrary common
interval. It is the translation-invariant form used for bounded predicates. -/
theorem card_lt_strongPairIterationFamilySize_of_real_separated_of_bounds
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    {mesh lowerBound upperBound : ℝ} {family : Finset (Row → ℝ)}
    {activeRows : Finset Row} {dimension steps : ℕ}
    (hmesh : 0 < mesh) (hsteps : steps ≤ activeRows.card)
    (hcount : strongShatteringPairBound (Fintype.card Row)
      (floorDiscretization mesh (upperBound - lowerBound) + 1) dimension <
        2 ^ steps)
    (hlower : ∀ f ∈ family, ∀ row ∈ activeRows, lowerBound ≤ f row)
    (hupper : ∀ f ∈ family, ∀ row ∈ activeRows, f row ≤ upperBound)
    (hseparated : ∀ f ∈ family, ∀ g ∈ family, f ≠ g →
      ∃ row ∈ activeRows, 2 * mesh ≤ |f row - g row|)
    (hfat : HasFatShatteringDimensionAtMostOn
      family activeRows (mesh / 2) dimension) :
    family.card < strongPairIterationFamilySize activeRows.card
      (floorDiscretization mesh (upperBound - lowerBound) + 1) steps := by
  let translated := translatedRealFamily (-lowerBound) family
  have htranslated := card_lt_strongPairIterationFamilySize_of_real_separated
    (family := translated) (activeRows := activeRows)
    (mesh := mesh) (upperBound := upperBound - lowerBound)
    (dimension := dimension) (steps := steps)
    hmesh hsteps hcount
    (by
      intro f hf row hrow
      obtain ⟨original, horiginal, rfl⟩ :=
        mem_translatedRealFamily.mp hf
      dsimp
      linarith [hlower original horiginal row hrow])
    (by
      intro f hf row hrow
      obtain ⟨original, horiginal, rfl⟩ :=
        mem_translatedRealFamily.mp hf
      dsimp
      linarith [hupper original horiginal row hrow])
    (translatedRealFamily_separated hseparated)
    (translatedRealFamily_hasFatShatteringDimensionAtMostOn hfat)
  rw [card_translatedRealFamily] at htranslated
  exact htranslated

end NormFormula
