import NormFormula.Combinatorics.HyperplaneArrangement

/-!
# Multirow threshold traces

For each row, fix a finite list of affine forms and a threshold.  This file
combines the two shifted copies of all row lists into one affine arrangement.
Its sign profile determines the complete set of rows whose maximum absolute
value reaches the prescribed threshold.  The number of realizable threshold
traces is therefore bounded by the arrangement face count.
-/

namespace NormFormula.HalfGraph

/-- An index consists of a row, a form in that row's finite list, and one of
the two threshold shifts. -/
abbrev RowThresholdIndex {ρ : Type*} [Fintype ρ] {ℓ : ℕ}
    (forms : ρ → Finset (AffineForm ℓ)) :=
  Σ r : ρ, (forms r : Type) ⊕ (forms r : Type)

/-- The single affine arrangement obtained by combining the shifted lists for
all rows. -/
def rowThresholdArrangement {ρ : Type*} [Fintype ρ] {ℓ : ℕ}
    (forms : ρ → Finset (AffineForm ℓ)) (threshold : ρ → ℝ) :
    RowThresholdIndex forms → AffineForm ℓ :=
  fun i ↦ thresholdSignForms (fun f : forms i.1 ↦ f.1) (threshold i.1) i.2

/-- The threshold trace at an amplitude vector: the finite set of rows whose
list contains a form with absolute value at least the row threshold. -/
noncomputable def rowThresholdTrace {ρ : Type*} [Fintype ρ] {ℓ : ℕ}
    (forms : ρ → Finset (AffineForm ℓ)) (threshold : ρ → ℝ)
    (t : Fin ℓ → ℝ) : Finset ρ := by
  classical
  exact Finset.univ.filter fun r ↦
    ∃ f : forms r, threshold r ≤ |f.1.eval t|

/-- Read a row threshold trace directly from a sign profile of the combined
arrangement. -/
noncomputable def rowThresholdTraceOfProfile
    {ρ : Type*} [Fintype ρ] {ℓ : ℕ}
    (forms : ρ → Finset (AffineForm ℓ))
    (s : RowThresholdIndex forms → SignType) : Finset ρ := by
  classical
  exact Finset.univ.filter fun r ↦ ∃ f : forms r,
    0 ≤ s ⟨r, Sum.inl f⟩ ∨ s ⟨r, Sum.inr f⟩ ≤ 0

/-- Evaluating `rowThresholdTraceOfProfile` on the actual arrangement profile
recovers the numerical threshold trace. -/
theorem rowThresholdTrace_eq_traceOfProfile
    {ρ : Type*} [Fintype ρ] {ℓ : ℕ}
    (forms : ρ → Finset (AffineForm ℓ)) (threshold : ρ → ℝ)
    (t : Fin ℓ → ℝ) :
    rowThresholdTrace forms threshold t =
      rowThresholdTraceOfProfile forms
        (affineSignProfile (rowThresholdArrangement forms threshold) t) := by
  classical
  ext r
  simp only [rowThresholdTrace, rowThresholdTraceOfProfile,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    simpa [affineSignProfile, rowThresholdArrangement, thresholdSignForms] using
      (le_abs_eval_iff_threshold_signs f.1 (threshold r) t).mp hf
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    apply (le_abs_eval_iff_threshold_signs f.1 (threshold r) t).mpr
    simpa [affineSignProfile, rowThresholdArrangement, thresholdSignForms] using hf

/-- All threshold traces realized by sign faces of the combined arrangement. -/
noncomputable def realizableRowThresholdTraces
    {ρ : Type*} [Fintype ρ] {ℓ : ℕ}
    (forms : ρ → Finset (AffineForm ℓ)) (threshold : ρ → ℝ) :
    Finset (Finset ρ) := by
  classical
  exact (realizableAffineSignPatterns
    (rowThresholdArrangement forms threshold)).image
      (rowThresholdTraceOfProfile forms)

@[simp]
theorem mem_realizableRowThresholdTraces
    {ρ : Type*} [Fintype ρ] {ℓ : ℕ}
    (forms : ρ → Finset (AffineForm ℓ)) (threshold : ρ → ℝ)
    (trace : Finset ρ) :
    trace ∈ realizableRowThresholdTraces forms threshold ↔
      ∃ t, rowThresholdTrace forms threshold t = trace := by
  classical
  rw [realizableRowThresholdTraces, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rcases (mem_realizableAffineSignPatterns _ s).mp hs with ⟨t, rfl⟩
    exact ⟨t, rowThresholdTrace_eq_traceOfProfile forms threshold t⟩
  · rintro ⟨t, rfl⟩
    refine ⟨affineSignProfile (rowThresholdArrangement forms threshold) t, ?_, ?_⟩
    · exact (mem_realizableAffineSignPatterns _ _).mpr ⟨t, rfl⟩
    · exact (rowThresholdTrace_eq_traceOfProfile forms threshold t).symm

/-- The number of row-threshold traces is at most the exact face bound for
the combined arrangement. -/
theorem card_realizableRowThresholdTraces_le_faceBound
    {ρ : Type*} [Fintype ρ] {ℓ : ℕ}
    (forms : ρ → Finset (AffineForm ℓ)) (threshold : ρ → ℝ) :
    (realizableRowThresholdTraces forms threshold).card ≤
      hyperplaneFaceBound (Fintype.card (RowThresholdIndex forms)) ℓ := by
  classical
  calc
    (realizableRowThresholdTraces forms threshold).card ≤
        (realizableAffineSignPatterns
          (rowThresholdArrangement forms threshold)).card := by
      exact Finset.card_image_le
    _ ≤ hyperplaneFaceBound (Fintype.card (RowThresholdIndex forms)) ℓ :=
      card_realizableAffineSignPatterns_le_hyperplaneFaceBound_fintype _

/-- Exact cardinality of the combined row/shift index type. -/
theorem card_rowThresholdIndex
    {ρ : Type*} [Fintype ρ] {ℓ : ℕ}
    (forms : ρ → Finset (AffineForm ℓ)) :
    Fintype.card (RowThresholdIndex forms) =
      ∑ r, 2 * (forms r).card := by
  simp [RowThresholdIndex, Fintype.card_sigma, two_mul]

/-- A uniform bound on each row list gives a linear bound on the number of
hyperplanes in the combined arrangement. -/
theorem card_rowThresholdIndex_le
    {ρ : Type*} [Fintype ρ] {ℓ L : ℕ}
    (forms : ρ → Finset (AffineForm ℓ))
    (hforms : ∀ r, (forms r).card ≤ L) :
    Fintype.card (RowThresholdIndex forms) ≤ Fintype.card ρ * (2 * L) := by
  rw [card_rowThresholdIndex]
  calc
    (∑ r, 2 * (forms r).card) ≤ ∑ _r : ρ, 2 * L := by
      apply Finset.sum_le_sum
      intro r hr
      exact Nat.mul_le_mul_left 2 (hforms r)
    _ = Fintype.card ρ * (2 * L) := by simp

/-- Polynomial trace bound when every row list is nonempty and has at most
`L` forms. -/
theorem card_realizableRowThresholdTraces_le_polynomial
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] {ℓ L : ℕ}
    (forms : ρ → Finset (AffineForm ℓ)) (threshold : ρ → ℝ)
    (hforms : ∀ r, (forms r).card ≤ L)
    (hnonempty : ∀ r, (forms r).Nonempty) :
    (realizableRowThresholdTraces forms threshold).card ≤
      (ℓ + 1) * (2 * (Fintype.card ρ * (2 * L))) ^ ℓ := by
  have hindexPos : 0 < Fintype.card (RowThresholdIndex forms) := by
    rw [Fintype.card_pos_iff]
    let r : ρ := Classical.choice (inferInstance : Nonempty ρ)
    rcases hnonempty r with ⟨f, hf⟩
    exact ⟨⟨r, Sum.inl ⟨f, hf⟩⟩⟩
  have hindexLe := card_rowThresholdIndex_le forms hforms
  calc
    (realizableRowThresholdTraces forms threshold).card ≤
        hyperplaneFaceBound (Fintype.card (RowThresholdIndex forms)) ℓ :=
      card_realizableRowThresholdTraces_le_faceBound forms threshold
    _ ≤ (ℓ + 1) *
        (2 * Fintype.card (RowThresholdIndex forms)) ^ ℓ :=
      hyperplaneFaceBound_le_polynomial hindexPos
    _ ≤ (ℓ + 1) * (2 * (Fintype.card ρ * (2 * L))) ^ ℓ := by
      exact Nat.mul_le_mul_left (ℓ + 1)
        (pow_le_pow_left' (Nat.mul_le_mul_left 2 hindexLe) ℓ)

end NormFormula.HalfGraph
