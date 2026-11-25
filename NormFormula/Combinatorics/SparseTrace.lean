import NormFormula.Combinatorics.ThresholdTrace

/-!
# Threshold traces for one sparse order type

Fix the copies and labelled numerical positions of `ℓ` parameter coordinates.
For every row, the symbolic `q` construction supplies a finite affine list on
the common amplitude space `ℝ^ℓ`.  This file combines those lists across the
rows and applies the multirow arrangement theorem.  The resulting trace bound
has degree `ℓ` in the number of rows; the later sum over sparse order types
contributes a second degree-`ℓ` factor. These sharper estimates are
supplementary; the paper uses `ElementarySparseTrace` instead.
-/

namespace NormFormula.HalfGraph


/-- The symbolic affine list attached to each row for one fixed labelled
parameter realization. -/
noncomputable def symbolicRowQForms
    {ρ : Type*} [Fintype ρ] {ℓ : ℕ}
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ) :
    ρ → Finset (AffineForm ℓ) :=
  fun r ↦ symbolicAffineQForms
    (fun n ↦ rowU r n) (fun n ↦ rowV r n)
    (firstSupport r) (secondSupport r) copy index


/-- The complete threshold trace for one fixed labelled sparse type. -/
noncomputable def fixedTypeSymbolicThresholdTrace
    {ρ : Type*} [Fintype ρ] {ℓ : ℕ}
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (threshold : ρ → ℝ) (t : Fin ℓ → ℝ) : Finset ρ :=
  rowThresholdTrace
    (symbolicRowQForms rowU rowV firstSupport secondSupport copy index)
    threshold t

/-- The finite collection of threshold traces realized by the amplitude
vectors in one fixed sparse type. -/
noncomputable def realizableFixedTypeSymbolicThresholdTraces
    {ρ : Type*} [Fintype ρ] {ℓ : ℕ}
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (threshold : ρ → ℝ) : Finset (Finset ρ) :=
  realizableRowThresholdTraces
    (symbolicRowQForms rowU rowV firstSupport secondSupport copy index)
    threshold

@[simp]
theorem mem_realizableFixedTypeSymbolicThresholdTraces
    {ρ : Type*} [Fintype ρ] {ℓ : ℕ}
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (threshold : ρ → ℝ) (trace : Finset ρ) :
    trace ∈ realizableFixedTypeSymbolicThresholdTraces
      rowU rowV firstSupport secondSupport copy index threshold ↔
      ∃ t, fixedTypeSymbolicThresholdTrace
        rowU rowV firstSupport secondSupport copy index threshold t = trace := by
  exact mem_realizableRowThresholdTraces _ _ _

/-- Membership in the symbolic trace is the actual `q` threshold whenever
the supplied two coordinate sequences have the prescribed affine evaluations. -/
theorem mem_fixedTypeSymbolicThresholdTrace_iff_qSeminorm
    {ρ : Type*} [Fintype ρ] {ℓ : ℕ}
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (threshold : ρ → ℝ) (t : Fin ℓ → ℝ) (r : ρ)
    (u v : RealL2)
    (hrowU : ∀ n, n ∉ firstSupport r → rowU r n = 0)
    (hrowV : ∀ n, n ∉ secondSupport r → rowV r n = 0)
    (hu : ∀ n, u n =
      (labelledCoordinateForm (fun i ↦ rowU r i) copy index .first n).eval t)
    (hv : ∀ n, v n =
      (labelledCoordinateForm (fun i ↦ rowV r i) copy index .second n).eval t) :
    r ∈ fixedTypeSymbolicThresholdTrace
      rowU rowV firstSupport secondSupport copy index threshold t ↔
      threshold r ≤ qSeminorm (WithLp.toLp 2 (u, v)) := by
  classical
  rw [fixedTypeSymbolicThresholdTrace, rowThresholdTrace, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  have hq := qSeminorm_ge_iff_exists_symbolicAffineQForm
    (rowU r) (rowV r) u v (firstSupport r) (secondSupport r)
    copy index t (threshold r) hrowU hrowV hu hv
  constructor
  · rintro ⟨f, hf⟩
    apply hq.mpr
    exact ⟨f.1, f.2, hf⟩
  · intro h
    rcases hq.mp h with ⟨f, hf, hft⟩
    exact ⟨⟨f, hf⟩, hft⟩


end NormFormula.HalfGraph
