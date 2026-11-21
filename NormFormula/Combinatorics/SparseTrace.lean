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

/-- Uniform upper bound for one row's symbolic affine `q` list when the total
row support size is at most `m`. -/
def symbolicRowFormBound (m ℓ : ℕ) : ℕ :=
  1 + (m + ℓ) * (m + ℓ) + (m + ℓ) + (m + ℓ)

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

/-- Every symbolic row list contains the zero affine form. -/
theorem symbolicRowQForms_nonempty
    {ρ : Type*} [Fintype ρ] {ℓ : ℕ}
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ) (r : ρ) :
    (symbolicRowQForms rowU rowV firstSupport secondSupport copy index r).Nonempty := by
  refine ⟨AffineForm.zero ℓ, ?_⟩
  simp [symbolicRowQForms, symbolicAffineQForms]

/-- The symbolic list bound depends only on the total row support bound and
the number of parameter labels. -/
theorem card_symbolicRowQForms_le
    {ρ : Type*} [Fintype ρ] {ℓ m : ℕ}
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (hsupport : ∀ r, (firstSupport r).card + (secondSupport r).card ≤ m)
    (r : ρ) :
    (symbolicRowQForms rowU rowV firstSupport secondSupport copy index r).card ≤
      symbolicRowFormBound m ℓ := by
  have hforms := card_symbolicAffineQForms_le
    (fun n ↦ rowU r n) (fun n ↦ rowV r n)
    (firstSupport r) (secondSupport r) copy index
  have hs := hsupport r
  have hA : (firstSupport r).card ≤ m := by
    omega
  have hB : (secondSupport r).card ≤ m := by
    omega
  have hAℓ : (firstSupport r).card + ℓ ≤ m + ℓ := Nat.add_le_add_right hA ℓ
  have hBℓ : (secondSupport r).card + ℓ ≤ m + ℓ := Nat.add_le_add_right hB ℓ
  have hmul := Nat.mul_le_mul hAℓ hBℓ
  unfold symbolicRowQForms symbolicRowFormBound
  omega

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

/-- Exact arrangement bound for the traces realized inside one fixed sparse
type. -/
theorem card_realizableFixedTypeSymbolicThresholdTraces_le_faceBound
    {ρ : Type*} [Fintype ρ] {ℓ : ℕ}
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (threshold : ρ → ℝ) :
    (realizableFixedTypeSymbolicThresholdTraces
      rowU rowV firstSupport secondSupport copy index threshold).card ≤
      hyperplaneFaceBound
        (Fintype.card (RowThresholdIndex
          (symbolicRowQForms rowU rowV firstSupport secondSupport copy index))) ℓ :=
  card_realizableRowThresholdTraces_le_faceBound _ threshold

/-- Polynomial trace bound of degree `ℓ` in the number of rows for one fixed
sparse order type. -/
theorem card_realizableFixedTypeSymbolicThresholdTraces_le_polynomial
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] {ℓ m : ℕ}
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (threshold : ρ → ℝ)
    (hsupport : ∀ r, (firstSupport r).card + (secondSupport r).card ≤ m) :
    (realizableFixedTypeSymbolicThresholdTraces
      rowU rowV firstSupport secondSupport copy index threshold).card ≤
      (ℓ + 1) *
        (2 * (Fintype.card ρ * (2 * symbolicRowFormBound m ℓ))) ^ ℓ := by
  exact card_realizableRowThresholdTraces_le_polynomial
    (symbolicRowQForms rowU rowV firstSupport secondSupport copy index)
    threshold
    (card_symbolicRowQForms_le rowU rowV firstSupport secondSupport
      copy index hsupport)
    (symbolicRowQForms_nonempty rowU rowV firstSupport secondSupport copy index)

end NormFormula.HalfGraph
