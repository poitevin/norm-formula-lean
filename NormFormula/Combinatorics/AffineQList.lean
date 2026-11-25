import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring
import NormFormula.Combinatorics.FiniteSupportQ
import NormFormula.Combinatorics.SparseOrderType

/-!
# Fixed affine lists for sparse parameters

This file packages the bridge from the finite-support formula for `q` to the
finite threshold-trace counts.  Once finite candidate supports are fixed,
`q` is the maximum of a fixed finite list of absolute affine forms.  The
candidate supports are allowed to overestimate the actual supports, so the
statement remains true when a parameter amplitude cancels a row coordinate.
-/

namespace NormFormula.HalfGraph

/-- A concrete affine function on the amplitude space `ℝ^ℓ`, represented by
its constant term and its `ℓ` coefficients. -/
structure AffineForm (ℓ : ℕ) where
  constant : ℝ
  coeff : Fin ℓ → ℝ

namespace AffineForm

@[ext]
theorem ext {ℓ : ℕ} {f g : AffineForm ℓ}
    (hconstant : f.constant = g.constant)
    (hcoeff : ∀ a, f.coeff a = g.coeff a) : f = g := by
  cases f with
  | mk fc ff =>
      cases g with
      | mk gc gf =>
          simp only at hconstant hcoeff ⊢
          subst gc
          congr
          funext a
          exact hcoeff a

/-- Evaluate an affine form at an amplitude vector. -/
def eval {ℓ : ℕ} (f : AffineForm ℓ) (t : Fin ℓ → ℝ) : ℝ :=
  f.constant + ∑ a, f.coeff a * t a

/-- The zero affine form. -/
def zero (ℓ : ℕ) : AffineForm ℓ :=
  ⟨0, fun _ ↦ 0⟩

/-- Pointwise addition of affine forms. -/
def add {ℓ : ℕ} (f g : AffineForm ℓ) : AffineForm ℓ :=
  ⟨f.constant + g.constant, fun a ↦ f.coeff a + g.coeff a⟩

@[simp]
theorem eval_zero (ℓ : ℕ) (t : Fin ℓ → ℝ) : (zero ℓ).eval t = 0 := by
  simp [eval, zero]

@[simp]
theorem eval_add {ℓ : ℕ} (f g : AffineForm ℓ) (t : Fin ℓ → ℝ) :
    (add f g).eval t = f.eval t + g.eval t := by
  simp only [eval, add, add_mul, Finset.sum_add_distrib]
  ring

end AffineForm

/-- Affine forms coming from admissible pairs of candidate coordinates. -/
noncomputable def pairedQForms {ℓ : ℕ} (first second : ℕ → AffineForm ℓ)
    (A B : Finset ℕ) : Finset (AffineForm ℓ) := by
  classical
  exact A.biUnion fun a ↦
    (B.filter fun b ↦ a < b).image fun b ↦ AffineForm.add (first a) (second b)

/-- Affine forms coming from first-copy candidate coordinates. -/
noncomputable def firstOnlyQForms {ℓ : ℕ} (first : ℕ → AffineForm ℓ)
    (A : Finset ℕ) : Finset (AffineForm ℓ) := by
  classical
  exact A.image first

/-- Affine forms coming from second-copy candidates which have an earlier
position outside the candidate first support. -/
noncomputable def secondOnlyQForms {ℓ : ℕ} (second : ℕ → AffineForm ℓ)
    (A B : Finset ℕ) : Finset (AffineForm ℓ) := by
  classical
  exact (B.filter fun b ↦ hasZeroBefore A b).image second

/-- The fixed list of affine forms attached to candidate supports `A,B`. -/
noncomputable def finiteAffineQForms {ℓ : ℕ} (first second : ℕ → AffineForm ℓ)
    (A B : Finset ℕ) : Finset (AffineForm ℓ) := by
  classical
  exact insert (AffineForm.zero ℓ)
    (pairedQForms first second A B ∪ firstOnlyQForms first A ∪
      secondOnlyQForms second A B)

/-- Evaluate the fixed affine list and take absolute values. -/
noncomputable def finiteAffineQValues {ℓ : ℕ} (first second : ℕ → AffineForm ℓ)
    (A B : Finset ℕ) (t : Fin ℓ → ℝ) : Finset ℝ :=
  insert 0
    ((pairedQForms first second A B).image (fun f ↦ |f.eval t|) ∪
      (firstOnlyQForms first A).image (fun f ↦ |f.eval t|) ∪
      (secondOnlyQForms second A B).image (fun f ↦ |f.eval t|))

theorem finiteAffineQValues_nonempty {ℓ : ℕ} (first second : ℕ → AffineForm ℓ)
    (A B : Finset ℕ) (t : Fin ℓ → ℝ) :
    (finiteAffineQValues first second A B t).Nonempty := by
  exact ⟨0, by simp [finiteAffineQValues]⟩

/-- `finiteAffineQValues` is literally the image of the fixed affine list
under evaluation followed by absolute value. -/
theorem finiteAffineQValues_eq_image {ℓ : ℕ}
    (first second : ℕ → AffineForm ℓ) (A B : Finset ℕ)
    (t : Fin ℓ → ℝ) :
    finiteAffineQValues first second A B t =
      (finiteAffineQForms first second A B).image (fun f ↦ |f.eval t|) := by
  classical
  rw [finiteAffineQValues, finiteAffineQForms, Finset.image_insert,
    Finset.image_union, Finset.image_union]
  simp

/-- Evaluation of the paired affine forms gives the paired coordinate values. -/
theorem image_pairedQForms_eq_pairedQValues {ℓ : ℕ}
    (first second : ℕ → AffineForm ℓ) (u v : RealL2) (A B : Finset ℕ)
    (t : Fin ℓ → ℝ) (hfirst : ∀ a ∈ A, (first a).eval t = u a)
    (hsecond : ∀ b ∈ B, (second b).eval t = v b) :
    (pairedQForms first second A B).image (fun f ↦ |f.eval t|) =
      pairedQValues u v A B := by
  classical
  ext c
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨f, hf, rfl⟩
    rw [pairedQForms] at hf
    rcases Finset.mem_biUnion.mp hf with ⟨a, ha, haf⟩
    rcases Finset.mem_image.mp haf with ⟨b, hb, rfl⟩
    rw [AffineForm.eval_add, hfirst a ha, hsecond b (Finset.mem_filter.mp hb).1]
    rw [pairedQValues, Finset.mem_biUnion]
    exact ⟨a, ha, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩
  · intro hc
    rw [pairedQValues] at hc
    rcases Finset.mem_biUnion.mp hc with ⟨a, ha, hac⟩
    rcases Finset.mem_image.mp hac with ⟨b, hb, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨AffineForm.add (first a) (second b), ?_, ?_⟩
    · rw [pairedQForms, Finset.mem_biUnion]
      exact ⟨a, ha, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩
    · rw [AffineForm.eval_add, hfirst a ha, hsecond b (Finset.mem_filter.mp hb).1]

/-- Evaluation of the first-only affine forms gives the corresponding
one-coordinate values. -/
theorem image_firstOnlyQForms_eq_firstOnlyQValues {ℓ : ℕ}
    (first : ℕ → AffineForm ℓ) (u : RealL2) (A : Finset ℕ)
    (t : Fin ℓ → ℝ) (hfirst : ∀ a ∈ A, (first a).eval t = u a) :
    (firstOnlyQForms first A).image (fun f ↦ |f.eval t|) =
      firstOnlyQValues u A := by
  classical
  ext c
  simp only [firstOnlyQForms, firstOnlyQValues, Finset.mem_image]
  constructor
  · rintro ⟨f, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, by rw [hfirst a ha]⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨first a, ⟨a, ha, rfl⟩, by rw [hfirst a ha]⟩

/-- Evaluation of the second-only affine forms gives the corresponding
one-coordinate values. -/
theorem image_secondOnlyQForms_eq_secondOnlyQValues {ℓ : ℕ}
    (second : ℕ → AffineForm ℓ) (v : RealL2) (A B : Finset ℕ)
    (t : Fin ℓ → ℝ) (hsecond : ∀ b ∈ B, (second b).eval t = v b) :
    (secondOnlyQForms second A B).image (fun f ↦ |f.eval t|) =
      secondOnlyQValues v A B := by
  classical
  ext c
  simp only [secondOnlyQForms, secondOnlyQValues, Finset.mem_image]
  constructor
  · rintro ⟨f, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, by rw [hsecond b (Finset.mem_filter.mp hb).1]⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨second b, ⟨b, hb, rfl⟩,
      by rw [hsecond b (Finset.mem_filter.mp hb).1]⟩

/-- Evaluating the fixed affine list recovers the finite coordinate-value list. -/
theorem finiteAffineQValues_eq_finiteQValues {ℓ : ℕ}
    (first second : ℕ → AffineForm ℓ) (u v : RealL2) (A B : Finset ℕ)
    (t : Fin ℓ → ℝ) (hfirst : ∀ a ∈ A, (first a).eval t = u a)
    (hsecond : ∀ b ∈ B, (second b).eval t = v b) :
    finiteAffineQValues first second A B t = finiteQValues u v A B := by
  rw [finiteAffineQValues, finiteQValues,
    image_pairedQForms_eq_pairedQValues first second u v A B t hfirst hsecond,
    image_firstOnlyQForms_eq_firstOnlyQValues first u A t hfirst,
    image_secondOnlyQForms_eq_secondOnlyQValues second v A B t hsecond]


/-- On candidate supports, `q` is the maximum of a fixed finite list of
absolute affine forms.  The support-containment assumptions make the result
stable under all amplitude cancellations. -/
theorem qSeminorm_eq_max_finiteAffineQValues {ℓ : ℕ}
    (first second : ℕ → AffineForm ℓ) (u v : RealL2) (A B : Finset ℕ)
    (t : Fin ℓ → ℝ) (hA : ∀ i, i ∉ A → u i = 0)
    (hB : ∀ j, j ∉ B → v j = 0)
    (hfirst : ∀ a ∈ A, (first a).eval t = u a)
    (hsecond : ∀ b ∈ B, (second b).eval t = v b) :
    qSeminorm (WithLp.toLp 2 (u, v)) =
      (finiteAffineQValues first second A B t).max'
        (finiteAffineQValues_nonempty first second A B t) := by
  have hvalues :=
    finiteAffineQValues_eq_finiteQValues first second u v A B t hfirst hsecond
  have hq := qSeminorm_eq_max_finiteQValues_of_support_subset u v A B hA hB
  calc
    qSeminorm (WithLp.toLp 2 (u, v)) =
        (finiteQValues u v A B).max' (finiteQValues_nonempty u v A B) := hq
    _ = (finiteAffineQValues first second A B t).max'
        (finiteAffineQValues_nonempty first second A B t) := by
      apply le_antisymm
      · rw [Finset.max'_le_iff]
        intro c hc
        apply Finset.le_max'
        rwa [hvalues]
      · rw [Finset.max'_le_iff]
        intro c hc
        apply Finset.le_max'
        rwa [← hvalues]

/-- Numerical positions occupied by labels in one copy of `ℓ₂`. -/
def labelIndexSet {ℓ : ℕ} (copy : Fin ℓ → CoordinateCopy)
    (index : Fin ℓ → ℕ) (target : CoordinateCopy) : Finset ℕ :=
  (Finset.univ.filter fun a ↦ copy a = target).image index

/-- Candidate support obtained by adjoining the labelled parameter positions
to a row support. -/
def candidateSupport {ℓ : ℕ} (rowSupport : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (target : CoordinateCopy) : Finset ℕ :=
  rowSupport ∪ labelIndexSet copy index target

theorem card_labelIndexSet_le {ℓ : ℕ} (copy : Fin ℓ → CoordinateCopy)
    (index : Fin ℓ → ℕ) (target : CoordinateCopy) :
    (labelIndexSet copy index target).card ≤ ℓ := by
  unfold labelIndexSet
  exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans_eq (by simp))

theorem card_candidateSupport_le {ℓ : ℕ} (rowSupport : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (target : CoordinateCopy) :
    (candidateSupport rowSupport copy index target).card ≤ rowSupport.card + ℓ := by
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (card_labelIndexSet_le copy index target) _)

/-- The coordinate of a fixed row plus a labelled sparse parameter is an
affine form in the parameter amplitudes. -/
def labelledCoordinateForm {ℓ : ℕ} (row : ℕ → ℝ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (target : CoordinateCopy) (n : ℕ) : AffineForm ℓ where
  constant := row n
  coeff a := if copy a = target ∧ index a = n then 1 else 0

theorem labelledCoordinateForm_eval {ℓ : ℕ} (row : ℕ → ℝ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (target : CoordinateCopy) (n : ℕ) (t : Fin ℓ → ℝ) :
    (labelledCoordinateForm row copy index target n).eval t =
      row n + ∑ a, if copy a = target ∧ index a = n then t a else 0 := by
  simp [AffineForm.eval, labelledCoordinateForm]

/-- Outside the candidate support, the corresponding coordinate affine form
vanishes. -/
theorem labelledCoordinateForm_eval_eq_zero_of_not_mem {ℓ : ℕ}
    (row : ℕ → ℝ) (rowSupport : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (target : CoordinateCopy) (t : Fin ℓ → ℝ)
    (hrow : ∀ n, n ∉ rowSupport → row n = 0) {n : ℕ}
    (hn : n ∉ candidateSupport rowSupport copy index target) :
    (labelledCoordinateForm row copy index target n).eval t = 0 := by
  have hnrow : n ∉ rowSupport := by
    intro hnrow
    exact hn (Finset.mem_union_left _ hnrow)
  have hlabel : ∀ a, ¬(copy a = target ∧ index a = n) := by
    intro a ha
    apply hn
    apply Finset.mem_union_right
    rw [labelIndexSet, Finset.mem_image]
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.1⟩, ha.2⟩
  rw [labelledCoordinateForm_eval, hrow n hnrow]
  simp [hlabel]

/-- Specialization of the affine-list theorem to a fixed row plus `ℓ`
labelled parameter amplitudes. The hypotheses `hu` and `hv` say precisely
that the two resulting sequences have the displayed affine coordinates. -/
theorem qSeminorm_eq_max_labelledAffineQValues {ℓ : ℕ}
    (rowU rowV u v : RealL2) (A₀ B₀ : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (t : Fin ℓ → ℝ)
    (hrowU : ∀ n, n ∉ A₀ → rowU n = 0)
    (hrowV : ∀ n, n ∉ B₀ → rowV n = 0)
    (hu : ∀ n, u n =
      (labelledCoordinateForm (fun i ↦ rowU i) copy index .first n).eval t)
    (hv : ∀ n, v n =
      (labelledCoordinateForm (fun i ↦ rowV i) copy index .second n).eval t) :
    qSeminorm (WithLp.toLp 2 (u, v)) =
      (finiteAffineQValues
        (labelledCoordinateForm (fun i ↦ rowU i) copy index .first)
        (labelledCoordinateForm (fun i ↦ rowV i) copy index .second)
        (candidateSupport A₀ copy index .first)
        (candidateSupport B₀ copy index .second) t).max'
      (finiteAffineQValues_nonempty
        (labelledCoordinateForm (fun i ↦ rowU i) copy index .first)
        (labelledCoordinateForm (fun i ↦ rowV i) copy index .second)
        (candidateSupport A₀ copy index .first)
        (candidateSupport B₀ copy index .second) t) := by
  apply qSeminorm_eq_max_finiteAffineQValues
  · intro n hn
    rw [hu n]
    exact labelledCoordinateForm_eval_eq_zero_of_not_mem
      (fun i ↦ rowU i) A₀ copy index .first t hrowU hn
  · intro n hn
    rw [hv n]
    exact labelledCoordinateForm_eval_eq_zero_of_not_mem
      (fun i ↦ rowV i) B₀ copy index .second t hrowV hn
  · intro a ha
    exact (hu a).symm
  · intro b hb
    exact (hv b).symm


end NormFormula.HalfGraph
