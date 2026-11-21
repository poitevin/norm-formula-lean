import NormFormula.Combinatorics.HyperplaneInsertion

/-!
# The affine-hyperplane face bound

This file completes the standard insertion induction.  A constant affine form
does not increase the number of sign faces.  A nonconstant affine form creates
at most twice as many new faces as occur in its restricted arrangement in one
lower dimension.  The resulting recurrence is exactly `hyperplaneFaceBound`.
-/

namespace NormFormula.HalfGraph

/-- Reindex sign profiles along an equivalence of finite index types. -/
def affineSignProfileReindexEmbedding {ι κ : Type*} (e : κ ≃ ι) :
    (ι → SignType) ↪ (κ → SignType) :=
  ⟨fun s k ↦ s (e k), by
    intro s s' h
    funext i
    have hi := congrFun h (e.symm i)
    simpa using hi⟩

theorem affineSignProfile_reindex {ι κ : Type*} {ℓ : ℕ}
    (e : κ ≃ ι) (forms : ι → AffineForm ℓ) (t : Fin ℓ → ℝ) :
    affineSignProfile (fun k ↦ forms (e k)) t =
      affineSignProfileReindexEmbedding e (affineSignProfile forms t) := by
  rfl

/-- Reindexing a finite arrangement maps its realizable profiles bijectively
onto those of the original arrangement. -/
theorem realizableAffineSignPatterns_reindex_eq_map
    {ι κ : Type*} [Fintype ι] [Fintype κ] {ℓ : ℕ}
    (e : κ ≃ ι) (forms : ι → AffineForm ℓ) :
    realizableAffineSignPatterns (fun k ↦ forms (e k)) =
      (realizableAffineSignPatterns forms).map
        (affineSignProfileReindexEmbedding e) := by
  classical
  ext u
  rw [mem_realizableAffineSignPatterns, Finset.mem_map]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨affineSignProfile forms t, ?_, ?_⟩
    · exact (mem_realizableAffineSignPatterns forms _).mpr ⟨t, rfl⟩
    · exact (affineSignProfile_reindex e forms t).symm
  · rintro ⟨s, hs, rfl⟩
    rcases (mem_realizableAffineSignPatterns forms s).mp hs with ⟨t, rfl⟩
    exact ⟨t, affineSignProfile_reindex e forms t⟩

/-- The number of relatively open faces cut out by `N` affine forms on
`ℝ^ℓ` is bounded by the exact hyperplane-arrangement expression from the
manuscript. -/
theorem card_realizableAffineSignPatterns_le_hyperplaneFaceBound
    {N ℓ : ℕ} (forms : Fin N → AffineForm ℓ) :
    (realizableAffineSignPatterns forms).card ≤ hyperplaneFaceBound N ℓ := by
  classical
  induction N generalizing ℓ with
  | zero =>
      rw [card_realizableAffineSignPatterns_no_forms,
        hyperplaneFaceBound_zero_forms]
  | succ N ih =>
      cases ℓ with
      | zero =>
          simpa only [hyperplaneFaceBound_zero_dim] using
            card_realizableAffineSignPatterns_zero_dim_le forms
      | succ ℓ =>
          let g : AffineForm (ℓ + 1) := forms 0
          let old : Fin N → AffineForm (ℓ + 1) := Fin.tail forms
          have hforms : Fin.cons g old = forms := by
            exact Fin.cons_self_tail forms
          calc
            (realizableAffineSignPatterns forms).card =
                (realizableAffineSignPatterns (Fin.cons g old)).card := by
              rw [hforms]
            _ ≤ hyperplaneFaceBound (N + 1) (ℓ + 1) := by
              by_cases hcoeff : ∀ k, g.coeff k = 0
              · calc
                  _ ≤ (realizableAffineSignPatterns old).card :=
                    card_realizableAffineSignPatterns_fin_cons_le_of_coeff_eq_zero
                      g old hcoeff
                  _ ≤ hyperplaneFaceBound N (ℓ + 1) := ih old
                  _ ≤ hyperplaneFaceBound (N + 1) (ℓ + 1) := by
                    rw [hyperplaneFaceBound_succ_forms_succ_dim N ℓ]
                    omega
              · simp only [not_forall] at hcoeff
                obtain ⟨k, hk⟩ := hcoeff
                calc
                  _ ≤ (realizableAffineSignPatterns old).card +
                      2 * (realizableAffineSignPatterns
                        (fun i ↦ (old i).restrictToZero g k)).card :=
                    card_realizableAffineSignPatterns_fin_cons_le_restricted
                      g old k hk
                  _ ≤ hyperplaneFaceBound N (ℓ + 1) +
                      2 * hyperplaneFaceBound N ℓ := by
                    exact Nat.add_le_add (ih old)
                      (Nat.mul_le_mul_left 2
                        (ih (fun i ↦ (old i).restrictToZero g k)))
                  _ = hyperplaneFaceBound (N + 1) (ℓ + 1) :=
                    (hyperplaneFaceBound_succ_forms_succ_dim N ℓ).symm

/-- Index-type-independent form of the exact arrangement bound. -/
theorem card_realizableAffineSignPatterns_le_hyperplaneFaceBound_fintype
    {ι : Type*} [Fintype ι] {ℓ : ℕ} (forms : ι → AffineForm ℓ) :
    (realizableAffineSignPatterns forms).card ≤
      hyperplaneFaceBound (Fintype.card ι) ℓ := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let finForms : Fin (Fintype.card ι) → AffineForm ℓ := fun k ↦ forms (e k)
  have hreindex : realizableAffineSignPatterns finForms =
      (realizableAffineSignPatterns forms).map
        (affineSignProfileReindexEmbedding e) := by
    exact realizableAffineSignPatterns_reindex_eq_map e forms
  calc
    (realizableAffineSignPatterns forms).card =
        (realizableAffineSignPatterns finForms).card := by
      rw [hreindex, Finset.card_map]
    _ ≤ hyperplaneFaceBound (Fintype.card ι) ℓ :=
      card_realizableAffineSignPatterns_le_hyperplaneFaceBound finForms

/-- Coarse polynomial form of the supplementary arrangement bound. -/
theorem card_realizableAffineSignPatterns_le_polynomial
    {N ℓ : ℕ} (forms : Fin N → AffineForm ℓ) (hN : 0 < N) :
    (realizableAffineSignPatterns forms).card ≤
      (ℓ + 1) * (2 * N) ^ ℓ :=
  (card_realizableAffineSignPatterns_le_hyperplaneFaceBound forms).trans
    (hyperplaneFaceBound_le_polynomial hN)

/-- Index-type-independent form of the coarse polynomial estimate. -/
theorem card_realizableAffineSignPatterns_le_polynomial_fintype
    {ι : Type*} [Fintype ι] {ℓ : ℕ} (forms : ι → AffineForm ℓ)
    (hι : 0 < Fintype.card ι) :
    (realizableAffineSignPatterns forms).card ≤
      (ℓ + 1) * (2 * Fintype.card ι) ^ ℓ :=
  (card_realizableAffineSignPatterns_le_hyperplaneFaceBound_fintype forms).trans
    (hyperplaneFaceBound_le_polynomial hι)

end NormFormula.HalfGraph
