import NormFormula.Combinatorics.HyperplaneSigns

/-!
# Multirow threshold traces

For each row, fix a finite list of affine forms and a threshold.  This file
combines the two shifted copies of all row lists into one affine arrangement.
Its sign profile determines the set of rows whose maximum absolute value
reaches the prescribed threshold.
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


end NormFormula.HalfGraph
