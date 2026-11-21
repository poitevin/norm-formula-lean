import NormFormula.Combinatorics.SparseTrace

/-!
# Union of traces over sparse order types

The fixed-type trace theorem is now summed over the finite space of sparse
order codes.  For every code we choose one representative labelled index
realization.  The transport theorem for symbolic affine lists shows that an
arbitrary realization has exactly the same trace collection as its chosen
representative.  We then also take the finite union over all label counts
`ℓ ≤ k`.
-/

namespace NormFormula.HalfGraph

/-- Copies and numerical indices for `ℓ` labelled parameter coordinates. -/
structure LabelledSparseRealization (ℓ : ℕ) where
  copy : Fin ℓ → CoordinateCopy
  index : Fin ℓ → ℕ

/-- The sparse order code of a labelled realization. -/
def LabelledSparseRealization.code {ℓ : ℕ} (D : Finset ℕ)
    (p : LabelledSparseRealization ℓ) : SparseOrderType D ℓ :=
  sparseOrderType D p.copy p.index

/-- A harmless fallback realization used for codes which are not numerically
realizable. -/
def defaultLabelledSparseRealization (ℓ : ℕ) : LabelledSparseRealization ℓ where
  copy := fun _ ↦ .first
  index := fun _ ↦ 0

/-- Choose one numerical realization of a sparse code when one exists. -/
noncomputable def sparseCodeRepresentative {ℓ : ℕ} (D : Finset ℕ)
    (τ : SparseOrderType D ℓ) : LabelledSparseRealization ℓ := by
  classical
  exact if h : ∃ p : LabelledSparseRealization ℓ, p.code D = τ then
      Classical.choose h
    else
      defaultLabelledSparseRealization ℓ

theorem sparseCodeRepresentative_code_eq {ℓ : ℕ} (D : Finset ℕ)
    (τ : SparseOrderType D ℓ)
    (h : ∃ p : LabelledSparseRealization ℓ, p.code D = τ) :
    (sparseCodeRepresentative D τ).code D = τ := by
  rw [sparseCodeRepresentative, dif_pos h]
  exact Classical.choose_spec h

/-- Threshold traces assigned to one sparse code via its chosen
representative. -/
noncomputable def tracesForSparseCode
    {ρ : Type*} [Fintype ρ] {ℓ : ℕ}
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (threshold : ρ → ℝ) (D : Finset ℕ) (τ : SparseOrderType D ℓ) :
    Finset (Finset ρ) :=
  let p := sparseCodeRepresentative D τ
  realizableFixedTypeSymbolicThresholdTraces
    rowU rowV firstSupport secondSupport p.copy p.index threshold

/-- All traces obtained from all sparse codes with exactly `ℓ` labels. -/
noncomputable def realizableFixedLabelSparseTypeTraces
    {ρ : Type*} [Fintype ρ] (ℓ : ℕ)
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (threshold : ρ → ℝ) (D : Finset ℕ) : Finset (Finset ρ) := by
  classical
  exact Finset.univ.biUnion fun τ : SparseOrderType D ℓ ↦
    tracesForSparseCode rowU rowV firstSupport secondSupport threshold D τ

/-- Equal sparse types give identical symbolic row lists simultaneously for
all rows. -/
theorem symbolicRowQForms_eq_of_sparseOrderType_eq
    {ρ : Type*} [Fintype ρ] {ℓ s : ℕ}
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    {D : Finset ℕ}
    (htype : sparseOrderType D copy index = sparseOrderType D copy' index')
    (hfirstD : ∀ r, firstSupport r ⊆ D)
    (hsecondD : ∀ r, secondSupport r ⊆ D)
    (hrowU : ∀ r n, n ∉ firstSupport r → rowU r n = 0)
    (hrowV : ∀ r n, n ∉ secondSupport r → rowV r n = 0)
    (hsize : ∀ r, (firstSupport r).card + ℓ ≤ s)
    (hprotected : Finset.range (s + 1) ⊆ D) :
    symbolicRowQForms rowU rowV firstSupport secondSupport copy index =
      symbolicRowQForms rowU rowV firstSupport secondSupport copy' index' := by
  funext r
  exact symbolicAffineQForms_eq_of_sparseOrderType_eq
    (fun n ↦ rowU r n) (fun n ↦ rowV r n) htype
    (hfirstD r) (hsecondD r) (hrowU r) (hrowV r)
    (hsize r) hprotected

/-- Every actual labelled realization is covered by the representative of its
sparse code. -/
theorem fixedTypeSymbolicThresholdTrace_mem_fixedLabelUnion
    {ρ : Type*} [Fintype ρ] {ℓ s : ℕ}
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (threshold : ρ → ℝ) (D : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (t : Fin ℓ → ℝ)
    (hfirstD : ∀ r, firstSupport r ⊆ D)
    (hsecondD : ∀ r, secondSupport r ⊆ D)
    (hrowU : ∀ r n, n ∉ firstSupport r → rowU r n = 0)
    (hrowV : ∀ r n, n ∉ secondSupport r → rowV r n = 0)
    (hsize : ∀ r, (firstSupport r).card + ℓ ≤ s)
    (hprotected : Finset.range (s + 1) ⊆ D) :
    fixedTypeSymbolicThresholdTrace
        rowU rowV firstSupport secondSupport copy index threshold t ∈
      realizableFixedLabelSparseTypeTraces ℓ
        rowU rowV firstSupport secondSupport threshold D := by
  classical
  let p : LabelledSparseRealization ℓ := ⟨copy, index⟩
  let τ : SparseOrderType D ℓ := p.code D
  let rep := sparseCodeRepresentative D τ
  have hexists : ∃ q : LabelledSparseRealization ℓ, q.code D = τ := ⟨p, rfl⟩
  have hrep : rep.code D = τ := sparseCodeRepresentative_code_eq D τ hexists
  have htype : sparseOrderType D copy index =
      sparseOrderType D rep.copy rep.index := by
    exact hrep.symm
  have hforms := symbolicRowQForms_eq_of_sparseOrderType_eq
    rowU rowV firstSupport secondSupport htype hfirstD hsecondD
    hrowU hrowV hsize hprotected
  have htrace : fixedTypeSymbolicThresholdTrace
      rowU rowV firstSupport secondSupport copy index threshold t =
      fixedTypeSymbolicThresholdTrace
        rowU rowV firstSupport secondSupport rep.copy rep.index threshold t := by
    unfold fixedTypeSymbolicThresholdTrace
    rw [hforms]
  rw [realizableFixedLabelSparseTypeTraces, Finset.mem_biUnion]
  refine ⟨τ, Finset.mem_univ τ, ?_⟩
  rw [tracesForSparseCode]
  exact (mem_realizableFixedTypeSymbolicThresholdTraces
    rowU rowV firstSupport secondSupport rep.copy rep.index threshold _).mpr
      ⟨t, htrace.symm⟩

/-- Summing the fixed-type bound over every code with `ℓ` labels. -/
theorem card_realizableFixedLabelSparseTypeTraces_le
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] {ℓ m : ℕ}
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (threshold : ρ → ℝ) (D : Finset ℕ)
    (hsupport : ∀ r, (firstSupport r).card + (secondSupport r).card ≤ m) :
    (realizableFixedLabelSparseTypeTraces ℓ
      rowU rowV firstSupport secondSupport threshold D).card ≤
      Fintype.card (SparseOrderType D ℓ) *
        ((ℓ + 1) *
          (2 * (Fintype.card ρ * (2 * symbolicRowFormBound m ℓ))) ^ ℓ) := by
  classical
  unfold realizableFixedLabelSparseTypeTraces
  apply Finset.card_biUnion_le_card_mul
  intro τ hτ
  unfold tracesForSparseCode
  exact card_realizableFixedTypeSymbolicThresholdTraces_le_polynomial
    rowU rowV firstSupport secondSupport
    (sparseCodeRepresentative D τ).copy (sparseCodeRepresentative D τ).index
    threshold hsupport

/-- All representative trace collections with at most `k` labels. -/
noncomputable def realizableBoundedLabelSparseTypeTraces
    {ρ : Type*} [Fintype ρ] (k : ℕ)
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (threshold : ρ → ℝ) (D : Finset ℕ) : Finset (Finset ρ) := by
  classical
  exact (Finset.range (k + 1)).biUnion fun ℓ ↦
    realizableFixedLabelSparseTypeTraces ℓ
      rowU rowV firstSupport secondSupport threshold D

/-- Every labelled realization with at most `k` coordinates belongs to the
bounded-label trace union. -/
theorem fixedTypeSymbolicThresholdTrace_mem_boundedLabelUnion
    {ρ : Type*} [Fintype ρ] {ℓ s k : ℕ}
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (threshold : ρ → ℝ) (D : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (t : Fin ℓ → ℝ) (hℓ : ℓ ≤ k)
    (hfirstD : ∀ r, firstSupport r ⊆ D)
    (hsecondD : ∀ r, secondSupport r ⊆ D)
    (hrowU : ∀ r n, n ∉ firstSupport r → rowU r n = 0)
    (hrowV : ∀ r n, n ∉ secondSupport r → rowV r n = 0)
    (hsize : ∀ r, (firstSupport r).card + ℓ ≤ s)
    (hprotected : Finset.range (s + 1) ⊆ D) :
    fixedTypeSymbolicThresholdTrace
        rowU rowV firstSupport secondSupport copy index threshold t ∈
      realizableBoundedLabelSparseTypeTraces k
        rowU rowV firstSupport secondSupport threshold D := by
  classical
  rw [realizableBoundedLabelSparseTypeTraces, Finset.mem_biUnion]
  refine ⟨ℓ, Finset.mem_range.mpr (by omega), ?_⟩
  exact fixedTypeSymbolicThresholdTrace_mem_fixedLabelUnion
    rowU rowV firstSupport secondSupport threshold D copy index t
    hfirstD hsecondD hrowU hrowV hsize hprotected

/-- Exact finite sum bound before simplifying it to a degree-`2k`
polynomial. -/
theorem card_realizableBoundedLabelSparseTypeTraces_le_sum
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] {k m : ℕ}
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (threshold : ρ → ℝ) (D : Finset ℕ)
    (hsupport : ∀ r, (firstSupport r).card + (secondSupport r).card ≤ m) :
    (realizableBoundedLabelSparseTypeTraces k
      rowU rowV firstSupport secondSupport threshold D).card ≤
      ∑ ℓ ∈ Finset.range (k + 1),
        Fintype.card (SparseOrderType D ℓ) *
          ((ℓ + 1) *
            (2 * (Fintype.card ρ * (2 * symbolicRowFormBound m ℓ))) ^ ℓ) := by
  classical
  unfold realizableBoundedLabelSparseTypeTraces
  calc
    _ ≤ ∑ ℓ ∈ Finset.range (k + 1),
        (realizableFixedLabelSparseTypeTraces ℓ
          rowU rowV firstSupport secondSupport threshold D).card :=
      Finset.card_biUnion_le
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      exact card_realizableFixedLabelSparseTypeTraces_le
        rowU rowV firstSupport secondSupport threshold D hsupport

end NormFormula.HalfGraph
