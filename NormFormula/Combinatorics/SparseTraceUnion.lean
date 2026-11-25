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


end NormFormula.HalfGraph
