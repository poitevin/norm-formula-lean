import NormFormula.Combinatorics.FiniteIPPattern

/-!
# Finite covers and separated evaluation families

This module records the elementary metric-counting layer needed for
continuous-connective closure. If each of two coordinate evaluation classes
has a finite sup-norm cover, a family separated in at least one coordinate
injects into the product of the two covers.
-/

namespace NormFormula

/-- A finite collection of functions covers the evaluations of a finite
parameter family in strict rowwise sup distance `radius`. -/
def IsEvaluationSupCover
    {Row Parameter : Type*} [Fintype Row]
    (value : Row → Parameter → ℝ)
    (parameters : Finset Parameter)
    (centers : Finset (Row → ℝ)) (radius : ℝ) : Prop :=
  ∀ parameter ∈ parameters, ∃ center ∈ centers,
    ∀ row, |value row parameter - center row| < radius

/-- A finite family of real-valued row functions is pairwise separated in
strict sup scale `separation`. -/
def IsPairwiseSeparatedEvaluationFamily
    {Row : Type*} (family : Finset (Row → ℝ))
    (separation : ℝ) : Prop :=
  ∀ f ∈ family, ∀ g ∈ family, f ≠ g →
    ∃ row, separation ≤ |f row - g row|

/-- Adding a function separated from every member preserves pairwise
separation. -/
theorem IsPairwiseSeparatedEvaluationFamily.insert
    {Row : Type*} [DecidableEq (Row → ℝ)]
    {family : Finset (Row → ℝ)}
    {separation : ℝ} {newFunction : Row → ℝ}
    (hfamily : IsPairwiseSeparatedEvaluationFamily family separation)
    (hnew : ∀ f ∈ family, ∃ row,
      separation ≤ |newFunction row - f row|) :
    IsPairwiseSeparatedEvaluationFamily
      (insert newFunction family) separation := by
  classical
  intro f hf g hg hfg
  simp only [Finset.mem_insert] at hf hg
  rcases hf with rfl | hf <;> rcases hg with rfl | hg
  · exact (hfg rfl).elim
  · exact hnew g hg
  · obtain ⟨row, hrow⟩ := hnew f hf
    exact ⟨row, by simpa [abs_sub_comm] using hrow⟩
  · exact hfamily f hf g hg hfg

/-- A uniform packing bound for all separated subfamilies of a finite
evaluation family produces a strict sup cover of the same size bound. -/
theorem exists_supCover_of_separated_subfamily_card_lt
    {Row : Type*} [Fintype Row]
    {evaluations : Finset (Row → ℝ)} {separation : ℝ} {bound : ℕ}
    (hseparation : 0 < separation)
    (hpacking : ∀ family ⊆ evaluations,
      IsPairwiseSeparatedEvaluationFamily family separation →
        family.card < bound) :
    ∃ centers : Finset (Row → ℝ),
      centers ⊆ evaluations ∧
      IsEvaluationSupCover (fun row f ↦ f row)
        evaluations centers separation ∧
      centers.card < bound := by
  classical
  let candidates := evaluations.powerset.filter fun centers ↦
    IsPairwiseSeparatedEvaluationFamily centers separation
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, IsPairwiseSeparatedEvaluationFamily]
  obtain ⟨centers, hmax⟩ := candidates.exists_maximal hcandidates
  have hcenters := hmax.1
  simp only [candidates, Finset.mem_filter, Finset.mem_powerset] at hcenters
  refine ⟨centers, hcenters.1, ?_, hpacking centers hcenters.1 hcenters.2⟩
  intro evaluation hevaluation
  by_contra hnotCovered
  push Not at hnotCovered
  have hinsertSeparated : IsPairwiseSeparatedEvaluationFamily
      (insert evaluation centers) separation := by
    apply hcenters.2.insert
    intro center hcenter
    exact hnotCovered center hcenter
  have hinsertCandidate : insert evaluation centers ∈ candidates := by
    simp [candidates, Finset.insert_subset_iff, hevaluation,
      hcenters.1, hinsertSeparated]
  have hevaluationNot : evaluation ∉ centers := by
    intro hevaluationMem
    obtain ⟨row, hrow⟩ := hnotCovered evaluation hevaluationMem
    simp at hrow
    exact (not_lt_of_ge hrow) hseparation
  exact hmax.not_gt hinsertCandidate
    (Finset.ssubset_insert hevaluationNot)

/-- Parameter-level form of the maximal-packing argument: it is enough to
bound separated subfamilies of the finite set of distinct evaluations. -/
theorem exists_evaluationSupCover_of_separated_subfamily_card_lt
    {Row Parameter : Type*} [Fintype Row]
    {value : Row → Parameter → ℝ} {parameters : Finset Parameter}
    {separation : ℝ} {bound : ℕ}
    (hseparation : 0 < separation)
    (hpacking : ∀ family ⊆
        parameters.image (fun parameter row ↦ value row parameter),
      IsPairwiseSeparatedEvaluationFamily family separation →
        family.card < bound) :
    ∃ centers : Finset (Row → ℝ),
      IsEvaluationSupCover value parameters centers separation ∧
      centers.card < bound := by
  classical
  let evaluations :=
    parameters.image (fun parameter row ↦ value row parameter)
  obtain ⟨centers, _, hcover, hcard⟩ :=
    exists_supCover_of_separated_subfamily_card_lt
      (evaluations := evaluations) hseparation (by
        intro family hfamily
        exact hpacking family hfamily)
  refine ⟨centers, ?_, hcard⟩
  intro parameter hparameter
  have hevaluation : (fun row ↦ value row parameter) ∈ evaluations := by
    exact Finset.mem_image.mpr ⟨parameter, hparameter, rfl⟩
  obtain ⟨center, hcenter, hclose⟩ := hcover _ hevaluation
  exact ⟨center, hcenter, hclose⟩

/-- Two coordinate covers bound the cardinality of a parameter family whose
evaluation pairs are separated in at least one coordinate. -/
theorem card_le_mul_card_of_coordinateSeparated_of_supCovers
    {Row Parameter : Type*} [Fintype Row]
    {f g : Row → Parameter → ℝ}
    {parameters : Finset Parameter}
    {fCenters gCenters : Finset (Row → ℝ)}
    {radius : ℝ}
    (hfCover : IsEvaluationSupCover f parameters fCenters radius)
    (hgCover : IsEvaluationSupCover g parameters gCenters radius)
    (hseparated : ∀ p ∈ parameters, ∀ q ∈ parameters, p ≠ q →
      ∃ row, radius + radius ≤
        max |f row p - f row q| |g row p - g row q|) :
    parameters.card ≤ fCenters.card * gCenters.card := by
  classical
  let P := ↥parameters
  have hfCover' : ∀ p : P, ∃ center ∈ fCenters,
      ∀ row, |f row p.1 - center row| < radius :=
    fun p ↦ hfCover p.1 p.2
  have hgCover' : ∀ p : P, ∃ center ∈ gCenters,
      ∀ row, |g row p.1 - center row| < radius :=
    fun p ↦ hgCover p.1 p.2
  choose fCenter hfCenterMem hfCenterClose using hfCover'
  choose gCenter hgCenterMem hgCenterClose using hgCover'
  let Code := ↥(fCenters ×ˢ gCenters)
  let code : P → Code := fun parameter ↦
    ⟨(fCenter parameter, gCenter parameter), Finset.mem_product.mpr
      ⟨hfCenterMem parameter, hgCenterMem parameter⟩⟩
  have hcodeInjective : Function.Injective code := by
    intro p q hcode
    by_contra hpq
    have hpqValues : p.1 ≠ q.1 := by
      intro hpqValues
      apply hpq
      exact Subtype.ext hpqValues
    obtain ⟨row, hrow⟩ :=
      hseparated p.1 p.2 q.1 q.2 hpqValues
    have hcodeValues := congrArg Subtype.val hcode
    have hfSame : fCenter p = fCenter q :=
      congrArg Prod.fst hcodeValues
    have hgSame : gCenter p = gCenter q :=
      congrArg Prod.snd hcodeValues
    have hfCloseP := hfCenterClose p row
    have hfCloseQ := hfCenterClose q row
    have hgCloseP := hgCenterClose p row
    have hgCloseQ := hgCenterClose q row
    have hfPair : |f row p.1 - f row q.1| < radius + radius := by
      calc
        |f row p.1 - f row q.1| =
            |(f row p.1 - fCenter p row) +
              (fCenter q row - f row q.1)| := by rw [hfSame]; ring_nf
        _ ≤ |f row p.1 - fCenter p row| +
              |fCenter q row - f row q.1| := abs_add_le _ _
        _ < radius + radius :=
          add_lt_add hfCloseP (by simpa [abs_sub_comm] using hfCloseQ)
    have hgPair : |g row p.1 - g row q.1| < radius + radius := by
      calc
        |g row p.1 - g row q.1| =
            |(g row p.1 - gCenter p row) +
              (gCenter q row - g row q.1)| := by rw [hgSame]; ring_nf
        _ ≤ |g row p.1 - gCenter p row| +
              |gCenter q row - g row q.1| := abs_add_le _ _
        _ < radius + radius :=
          add_lt_add hgCloseP (by simpa [abs_sub_comm] using hgCloseQ)
    have hmax :
        max |f row p.1 - f row q.1| |g row p.1 - g row q.1| <
          radius + radius := max_lt hfPair hgPair
    exact (not_lt_of_ge hrow) hmax
  calc
    parameters.card = Fintype.card P := (Fintype.card_coe parameters).symm
    _ ≤ Fintype.card Code := Fintype.card_le_of_injective code hcodeInjective
    _ = (fCenters ×ˢ gCenters).card := Fintype.card_coe _
    _ = fCenters.card * gCenters.card := Finset.card_product _ _

/-- Powerset-indexed specialization: coordinate separation of the evaluations
chosen for all subsets forces the product of any two coordinate cover sizes
to be at least `2^n`. -/
theorem two_pow_le_mul_card_of_powerset_coordinateSeparated_of_supCovers
    {n : ℕ} {Parameter : Type*}
    {f g : Fin n → Parameter → ℝ}
    (parameters : Finset (Fin n) → Parameter)
    {fCenters gCenters : Finset (Fin n → ℝ)} {radius : ℝ}
    (hfCover : IsEvaluationSupCover
      (fun row subset ↦ f row (parameters subset))
      Finset.univ fCenters radius)
    (hgCover : IsEvaluationSupCover
      (fun row subset ↦ g row (parameters subset))
      Finset.univ gCenters radius)
    (hseparated : ∀ S T, S ≠ T → ∃ row,
      radius + radius ≤
        max |f row (parameters S) - f row (parameters T)|
          |g row (parameters S) - g row (parameters T)|) :
    2 ^ n ≤ fCenters.card * gCenters.card := by
  have hcard := card_le_mul_card_of_coordinateSeparated_of_supCovers
    hfCover hgCover (by
      intro S _ T _ hST
      exact hseparated S T hST)
  simpa [Fintype.card_finset] using hcard

end NormFormula
