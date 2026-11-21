import NormFormula.Combinatorics.HyperplaneRestriction

/-!
# Inserting one affine hyperplane

This file turns the geometric crossing lemma into the counting recurrence for
one newly inserted affine hyperplane.  A pair records an old sign face together
with one sign of the new affine form.  A face not met by the new zero
hyperplane has at most one extension; a face which is met has at most three.
Consequently insertion creates at most two additional faces for every old face
cut by the new hyperplane.
-/

namespace NormFormula.HalfGraph

/-- The signs of `g` which occur over one fixed old sign face `s`. -/
noncomputable def newSignExtensions
    {ι : Type*} [Fintype ι] {ℓ : ℕ}
    (old : ι → AffineForm ℓ) (g : AffineForm ℓ) (s : ι → SignType) :
    Finset SignType := by
  classical
  exact Finset.univ.filter fun σ ↦
    ∃ t, affineSignProfile old t = s ∧ SignType.sign (g.eval t) = σ

@[simp]
theorem mem_newSignExtensions
    {ι : Type*} [Fintype ι] {ℓ : ℕ}
    (old : ι → AffineForm ℓ) (g : AffineForm ℓ)
    (s : ι → SignType) (σ : SignType) :
    σ ∈ newSignExtensions old g s ↔
      ∃ t, affineSignProfile old t = s ∧ SignType.sign (g.eval t) = σ := by
  classical
  simp [newSignExtensions]

/-- If the zero hyperplane of `g` misses an old face, only one strict side of
`g` can occur on that face. -/
theorem card_newSignExtensions_le_one_of_not_zeroSlice
    {ι : Type*} [Fintype ι] {ℓ : ℕ}
    (old : ι → AffineForm ℓ) (g : AffineForm ℓ) (s : ι → SignType)
    (hz : s ∉ zeroSliceSignPatterns old g) :
    (newSignExtensions old g s).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro σ hσ τ hτ
  rcases (mem_newSignExtensions old g s σ).mp hσ with ⟨x, hxs, hxσ⟩
  rcases (mem_newSignExtensions old g s τ).mp hτ with ⟨y, hys, hyτ⟩
  by_contra hστ
  have hsign : SignType.sign (g.eval x) ≠ SignType.sign (g.eval y) := by
    intro h
    apply hστ
    rw [← hxσ, ← hyτ]
    exact h
  have hxne : g.eval x ≠ 0 := by
    intro hx
    apply hz
    exact (mem_zeroSliceSignPatterns old g s).mpr ⟨x, hx, hxs⟩
  have hyne : g.eval y ≠ 0 := by
    intro hy
    apply hz
    exact (mem_zeroSliceSignPatterns old g s).mpr ⟨y, hy, hys⟩
  have hface : SameAffineSignFace old x y := hxs.trans hys.symm
  rcases lt_or_gt_of_ne hxne with hxneg | hxpos
  · have hypos : 0 < g.eval y := by
      rcases lt_or_gt_of_ne hyne with hyneg | hypos
      · exfalso
        apply hsign
        rw [sign_neg hxneg, sign_neg hyneg]
      · exact hypos
    rcases exists_zero_in_same_affineSignFace old g hface hxneg hypos with
      ⟨z, hxz, hgz⟩
    apply hz
    exact (mem_zeroSliceSignPatterns old g s).mpr
      ⟨z, hgz, hxz.symm.trans hxs⟩
  · have hyneg : g.eval y < 0 := by
      rcases lt_or_gt_of_ne hyne with hyneg | hypos
      · exact hyneg
      · exfalso
        apply hsign
        rw [sign_pos hxpos, sign_pos hypos]
    rcases exists_zero_in_same_affineSignFace old g hface.symm hyneg hxpos with
      ⟨z, hyz, hgz⟩
    apply hz
    exact (mem_zeroSliceSignPatterns old g s).mpr
      ⟨z, hgz, hyz.symm.trans hys⟩

/-- All realizable old-face/new-sign pairs.  Writing the set as a disjoint
union over old faces makes the insertion count transparent. -/
noncomputable def insertedAffineSignPairs
    {ι : Type*} [Fintype ι] {ℓ : ℕ}
    (old : ι → AffineForm ℓ) (g : AffineForm ℓ) :
    Finset ((ι → SignType) × SignType) := by
  classical
  exact (realizableAffineSignPatterns old).biUnion fun s ↦
    {s} ×ˢ newSignExtensions old g s

@[simp]
theorem mem_insertedAffineSignPairs
    {ι : Type*} [Fintype ι] {ℓ : ℕ}
    (old : ι → AffineForm ℓ) (g : AffineForm ℓ)
    (p : (ι → SignType) × SignType) :
    p ∈ insertedAffineSignPairs old g ↔
      ∃ t, affineSignProfile old t = p.1 ∧
        SignType.sign (g.eval t) = p.2 := by
  classical
  constructor
  · intro hp
    rw [insertedAffineSignPairs, Finset.mem_biUnion] at hp
    rcases hp with ⟨s, hs, hp⟩
    rw [Finset.mem_product, Finset.mem_singleton] at hp
    rcases (mem_newSignExtensions old g s p.2).mp hp.2 with ⟨t, hts, htg⟩
    exact ⟨t, hts.trans hp.1.symm, htg⟩
  · rintro ⟨t, htp, htg⟩
    rw [insertedAffineSignPairs, Finset.mem_biUnion]
    refine ⟨p.1, ?_, ?_⟩
    · exact (mem_realizableAffineSignPatterns old p.1).mpr ⟨t, htp⟩
    · rw [Finset.mem_product, Finset.mem_singleton]
      exact ⟨rfl, (mem_newSignExtensions old g p.1 p.2).mpr ⟨t, htp, htg⟩⟩

/-- Prepending the sign of the new form turns an old-profile/new-sign pair
into the sign profile of the inserted arrangement. -/
def insertedFinProfileEmbedding {N : ℕ} :
    ((Fin N → SignType) × SignType) ↪ (Fin (N + 1) → SignType) :=
  ⟨fun p ↦ Fin.cons p.2 p.1, by
    rintro ⟨s, σ⟩ ⟨s', σ'⟩ h
    apply Prod.ext
    · funext i
      exact congrFun h i.succ
    · exact congrFun h 0⟩

/-- The profile of a `Fin.cons` arrangement is obtained by prepending the new
sign to the old profile. -/
theorem affineSignProfile_fin_cons {N ℓ : ℕ}
    (g : AffineForm ℓ) (old : Fin N → AffineForm ℓ) (t : Fin ℓ → ℝ) :
    affineSignProfile (Fin.cons g old) t =
      insertedFinProfileEmbedding
        (affineSignProfile old t, SignType.sign (g.eval t)) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [affineSignProfile, insertedFinProfileEmbedding]
  · simp [affineSignProfile, insertedFinProfileEmbedding]

/-- The pair representation is exactly the realizable-pattern finset for the
arrangement obtained by prepending `g`. -/
theorem realizableAffineSignPatterns_fin_cons_eq_map {N ℓ : ℕ}
    (g : AffineForm ℓ) (old : Fin N → AffineForm ℓ) :
    realizableAffineSignPatterns (Fin.cons g old) =
      (insertedAffineSignPairs old g).map insertedFinProfileEmbedding := by
  classical
  ext u
  rw [mem_realizableAffineSignPatterns, Finset.mem_map]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨(affineSignProfile old t, SignType.sign (g.eval t)), ?_, ?_⟩
    · exact (mem_insertedAffineSignPairs old g _).mpr ⟨t, rfl, rfl⟩
    · exact (affineSignProfile_fin_cons g old t).symm
  · rintro ⟨p, hp, rfl⟩
    rcases (mem_insertedAffineSignPairs old g p).mp hp with ⟨t, htold, htg⟩
    refine ⟨t, ?_⟩
    rw [affineSignProfile_fin_cons]
    apply congrArg insertedFinProfileEmbedding
    exact Prod.ext htold htg

/-- The one-hyperplane insertion recurrence: the new arrangement has at most
the old number of faces plus two for every old face met by `g=0`. -/
theorem card_insertedAffineSignPairs_le
    {ι : Type*} [Fintype ι] {ℓ : ℕ}
    (old : ι → AffineForm ℓ) (g : AffineForm ℓ) :
    (insertedAffineSignPairs old g).card ≤
      (realizableAffineSignPatterns old).card +
        2 * (zeroSliceSignPatterns old g).card := by
  classical
  let oldPatterns := realizableAffineSignPatterns old
  let zeroPatterns := zeroSliceSignPatterns old g
  have hzeroSubset : zeroPatterns ⊆ oldPatterns := by
    intro s hs
    rcases (mem_zeroSliceSignPatterns old g s).mp hs with ⟨t, _hgt, hts⟩
    exact (mem_realizableAffineSignPatterns old s).mpr ⟨t, hts⟩
  have hdisjoint : (oldPatterns : Set (ι → SignType)).PairwiseDisjoint
      (fun s ↦ {s} ×ˢ newSignExtensions old g s) := by
    intro s hs s' hs' hne
    change Disjoint ({s} ×ˢ newSignExtensions old g s)
      ({s'} ×ˢ newSignExtensions old g s')
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_product, Finset.mem_singleton] at hp hp'
    exact hne (hp.1.symm.trans hp'.1)
  rw [insertedAffineSignPairs, Finset.card_biUnion hdisjoint]
  calc
    (∑ s ∈ oldPatterns, ({s} ×ˢ newSignExtensions old g s).card) =
        ∑ s ∈ oldPatterns, (newSignExtensions old g s).card := by simp
    _ ≤ ∑ s ∈ oldPatterns, if s ∈ zeroPatterns then 3 else 1 := by
      apply Finset.sum_le_sum
      intro s hs
      by_cases hz : s ∈ zeroPatterns
      · simp only [hz, if_true]
        exact (newSignExtensions old g s).card_le_univ.trans_eq (by decide)
      · simp only [hz, if_false]
        exact card_newSignExtensions_le_one_of_not_zeroSlice old g s hz
    _ = oldPatterns.card + 2 * zeroPatterns.card := by
      have hfilter : oldPatterns.filter (fun s ↦ s ∈ zeroPatterns) = zeroPatterns := by
        ext s
        simp only [Finset.mem_filter]
        constructor
        · exact fun hs ↦ hs.2
        · intro hs
          exact ⟨hzeroSubset hs, hs⟩
      calc
        _ = ∑ s ∈ oldPatterns, (1 + if s ∈ zeroPatterns then 2 else 0) := by
          apply Finset.sum_congr rfl
          intro s hs
          by_cases hz : s ∈ zeroPatterns <;> simp [hz]
        _ = oldPatterns.card +
            ∑ s ∈ oldPatterns, if s ∈ zeroPatterns then 2 else 0 := by
          rw [Finset.sum_add_distrib]
          simp
        _ = oldPatterns.card + 2 * zeroPatterns.card := by
          rw [← Finset.sum_filter, hfilter]
          simp [Nat.mul_comm]

/-- Direct form of the insertion recurrence for a `Fin`-indexed arrangement. -/
theorem card_realizableAffineSignPatterns_fin_cons_le {N ℓ : ℕ}
    (g : AffineForm ℓ) (old : Fin N → AffineForm ℓ) :
    (realizableAffineSignPatterns (Fin.cons g old)).card ≤
      (realizableAffineSignPatterns old).card +
        2 * (zeroSliceSignPatterns old g).card := by
  rw [realizableAffineSignPatterns_fin_cons_eq_map, Finset.card_map]
  exact card_insertedAffineSignPairs_le old g

/-- If the new hyperplane is nonconstant, its zero-slice term is the face
count of the restricted arrangement in one lower dimension. -/
theorem card_realizableAffineSignPatterns_fin_cons_le_restricted
    {N ℓ : ℕ} (g : AffineForm (ℓ + 1))
    (old : Fin N → AffineForm (ℓ + 1))
    (k : Fin (ℓ + 1)) (hk : g.coeff k ≠ 0) :
    (realizableAffineSignPatterns (Fin.cons g old)).card ≤
      (realizableAffineSignPatterns old).card +
        2 * (realizableAffineSignPatterns
          (fun i ↦ (old i).restrictToZero g k)).card := by
  rw [← zeroSliceSignPatterns_eq_restricted old g k hk]
  exact card_realizableAffineSignPatterns_fin_cons_le g old

/-- An affine form whose entire linear part vanishes has constant evaluation. -/
theorem AffineForm.eval_eq_constant_of_coeff_eq_zero {ℓ : ℕ}
    (g : AffineForm ℓ) (hcoeff : ∀ k, g.coeff k = 0)
    (t : Fin ℓ → ℝ) :
    g.eval t = g.constant := by
  simp [AffineForm.eval, hcoeff]

/-- Inserting a constant affine form does not increase the number of
realizable sign patterns. -/
theorem card_realizableAffineSignPatterns_fin_cons_le_of_coeff_eq_zero
    {N ℓ : ℕ} (g : AffineForm ℓ) (old : Fin N → AffineForm ℓ)
    (hcoeff : ∀ k, g.coeff k = 0) :
    (realizableAffineSignPatterns (Fin.cons g old)).card ≤
      (realizableAffineSignPatterns old).card := by
  classical
  rw [realizableAffineSignPatterns_fin_cons_eq_map, Finset.card_map]
  let target := realizableAffineSignPatterns old ×ˢ
    {SignType.sign g.constant}
  have hsubset : insertedAffineSignPairs old g ⊆ target := by
    intro p hp
    rcases (mem_insertedAffineSignPairs old g p).mp hp with ⟨t, htold, htg⟩
    rw [Finset.mem_product, Finset.mem_singleton]
    refine ⟨(mem_realizableAffineSignPatterns old p.1).mpr ⟨t, htold⟩, ?_⟩
    rw [← htg, g.eval_eq_constant_of_coeff_eq_zero hcoeff]
  calc
    (insertedAffineSignPairs old g).card ≤ target.card :=
      Finset.card_le_card hsubset
    _ = (realizableAffineSignPatterns old).card := by simp [target]

end NormFormula.HalfGraph
