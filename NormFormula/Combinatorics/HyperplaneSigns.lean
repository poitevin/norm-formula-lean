import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Sign.Basic
import NormFormula.Combinatorics.SymbolicQList

/-!
# Sign faces and the hyperplane face-count bound

This file sets up the sign-pattern language for affine hyperplane arrangements.
It proves that the threshold tests needed for `q` are constant on sign faces
and formalizes the exact numerical bound and recurrence used by the standard
arrangement induction.  The geometric proof that realizable sign patterns
satisfy the recurrence is developed downstream in `HyperplaneRestriction`
and `HyperplaneInsertion`.
-/

namespace NormFormula.HalfGraph

/-- Add a constant to an affine form. -/
def AffineForm.shift {ℓ : ℕ} (f : AffineForm ℓ) (c : ℝ) : AffineForm ℓ :=
  ⟨f.constant + c, f.coeff⟩

@[simp]
theorem AffineForm.eval_shift {ℓ : ℕ} (f : AffineForm ℓ)
    (c : ℝ) (t : Fin ℓ → ℝ) :
    (f.shift c).eval t = f.eval t + c := by
  simp [AffineForm.shift, AffineForm.eval]
  ring

/-- The sign vector of a family of affine forms at a point. -/
noncomputable def affineSignProfile {ι : Type*} {ℓ : ℕ}
    (forms : ι → AffineForm ℓ) (t : Fin ℓ → ℝ) : ι → SignType :=
  fun i ↦ SignType.sign ((forms i).eval t)

/-- All sign vectors realized by a finite indexed family of affine forms. -/
noncomputable def realizableAffineSignPatterns {ι : Type*} [Fintype ι] {ℓ : ℕ}
    (forms : ι → AffineForm ℓ) : Finset (ι → SignType) := by
  classical
  exact Finset.univ.filter fun s ↦ ∃ t, affineSignProfile forms t = s

@[simp]
theorem mem_realizableAffineSignPatterns {ι : Type*} [Fintype ι] {ℓ : ℕ}
    (forms : ι → AffineForm ℓ) (s : ι → SignType) :
    s ∈ realizableAffineSignPatterns forms ↔
      ∃ t, affineSignProfile forms t = s := by
  classical
  simp [realizableAffineSignPatterns]

/-- The trivial ambient bound, useful for base cases of the arrangement
induction. -/
theorem card_realizableAffineSignPatterns_le_pow_three
    {ι : Type*} [Fintype ι] {ℓ : ℕ} (forms : ι → AffineForm ℓ) :
    (realizableAffineSignPatterns forms).card ≤ 3 ^ Fintype.card ι := by
  classical
  calc
    (realizableAffineSignPatterns forms).card ≤
        Fintype.card (ι → SignType) := Finset.card_le_univ _
    _ = 3 ^ Fintype.card ι := by
      have hcard : Fintype.card SignType = 3 := by decide
      simp [hcard]

/-- In zero-dimensional amplitude space there is at most one realizable sign
pattern. -/
theorem card_realizableAffineSignPatterns_zero_dim_le
    {ι : Type*} [Fintype ι] (forms : ι → AffineForm 0) :
    (realizableAffineSignPatterns forms).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro s hs s' hs'
  rcases (mem_realizableAffineSignPatterns forms s).mp hs with ⟨t, rfl⟩
  rcases (mem_realizableAffineSignPatterns forms s').mp hs' with ⟨t', rfl⟩
  have htt' : t = t' := Subsingleton.elim _ _
  rw [htt']

/-- An arrangement with no forms has exactly one (empty) sign pattern. -/
theorem card_realizableAffineSignPatterns_no_forms {ℓ : ℕ}
    (forms : Fin 0 → AffineForm ℓ) :
    (realizableAffineSignPatterns forms).card = 1 := by
  have hle : (realizableAffineSignPatterns forms).card ≤ 1 :=
    Finset.card_le_one_of_subsingleton _
  have hnonempty : (realizableAffineSignPatterns forms).Nonempty := by
    refine ⟨affineSignProfile forms 0, ?_⟩
    exact (mem_realizableAffineSignPatterns forms _).mpr ⟨0, rfl⟩
  have hpos : 0 < (realizableAffineSignPatterns forms).card :=
    Finset.card_pos.mpr hnonempty
  omega

/-- Two points lie in the same relatively open face of an indexed arrangement
when every defining affine form has the same sign at both points. -/
def SameAffineSignFace {ι : Type*} {ℓ : ℕ}
    (forms : ι → AffineForm ℓ) (t t' : Fin ℓ → ℝ) : Prop :=
  affineSignProfile forms t = affineSignProfile forms t'

theorem sameAffineSignFace_refl {ι : Type*} {ℓ : ℕ}
    (forms : ι → AffineForm ℓ) (t : Fin ℓ → ℝ) :
    SameAffineSignFace forms t t := rfl

theorem sameAffineSignFace_symm {ι : Type*} {ℓ : ℕ}
    {forms : ι → AffineForm ℓ} {t t' : Fin ℓ → ℝ}
    (h : SameAffineSignFace forms t t') : SameAffineSignFace forms t' t :=
  h.symm

theorem sameAffineSignFace_trans {ι : Type*} {ℓ : ℕ}
    {forms : ι → AffineForm ℓ} {t t' t'' : Fin ℓ → ℝ}
    (h : SameAffineSignFace forms t t') (h' : SameAffineSignFace forms t' t'') :
    SameAffineSignFace forms t t'' := h.trans h'

/-- The two affine forms whose signs determine `c ≤ |f(t)|`. -/
def thresholdSignForms {ι : Type*} {ℓ : ℕ}
    (forms : ι → AffineForm ℓ) (c : ℝ) : ι ⊕ ι → AffineForm ℓ
  | .inl i => (forms i).shift (-c)
  | .inr i => (forms i).shift c

/-- The elementary two-hyperplane reduction of an absolute-value threshold. -/
theorem le_abs_eval_iff_threshold_signs {ℓ : ℕ}
    (f : AffineForm ℓ) (c : ℝ) (t : Fin ℓ → ℝ) :
    c ≤ |f.eval t| ↔
      0 ≤ SignType.sign ((f.shift (-c)).eval t) ∨
        SignType.sign ((f.shift c).eval t) ≤ 0 := by
  rw [AffineForm.eval_shift, AffineForm.eval_shift,
    sign_nonneg_iff, sign_nonpos_iff]
  constructor
  · intro h
    by_cases hx : 0 ≤ f.eval t
    · left
      rw [abs_of_nonneg hx] at h
      linarith
    · right
      have hx' : f.eval t ≤ 0 := le_of_not_ge hx
      rw [abs_of_nonpos hx'] at h
      linarith
  · rintro (h | h)
    · exact (by linarith : c ≤ f.eval t).trans (le_abs_self _)
    · exact (by linarith : c ≤ -f.eval t).trans (neg_le_abs _)

/-- Equality of the two shifted sign profiles preserves an individual
absolute-value threshold test. -/
theorem le_abs_eval_iff_of_threshold_profile_eq
    {ι : Type*} {ℓ : ℕ} (forms : ι → AffineForm ℓ) (c : ℝ)
    {t t' : Fin ℓ → ℝ}
    (hface : SameAffineSignFace (thresholdSignForms forms c) t t') (i : ι) :
    (c ≤ |(forms i).eval t| ↔ c ≤ |(forms i).eval t'|) := by
  rw [le_abs_eval_iff_threshold_signs, le_abs_eval_iff_threshold_signs]
  have hminus := congrFun hface (Sum.inl i)
  have hplus := congrFun hface (Sum.inr i)
  simp only [affineSignProfile, thresholdSignForms] at hminus hplus
  rw [hminus, hplus]

/-- A threshold test for the maximum absolute value of a finite indexed
family. -/
def affineMaxAbsGE {ι : Type*} (forms : ι → AffineForm ℓ)
    (c : ℝ) (t : Fin ℓ → ℝ) : Prop :=
  ∃ i, c ≤ |(forms i).eval t|

/-- The maximum-threshold test is constant on every sign face of the two
shifted copies of the affine list. -/
theorem affineMaxAbsGE_iff_of_same_threshold_face
    {ι : Type*} {ℓ : ℕ} (forms : ι → AffineForm ℓ) (c : ℝ)
    {t t' : Fin ℓ → ℝ}
    (hface : SameAffineSignFace (thresholdSignForms forms c) t t') :
    affineMaxAbsGE forms c t ↔ affineMaxAbsGE forms c t' := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (le_abs_eval_iff_of_threshold_profile_eq forms c hface i).mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (le_abs_eval_iff_of_threshold_profile_eq forms c hface i).mpr hi⟩

/-- Finset version of the preceding face-constancy theorem. -/
theorem finset_abs_threshold_iff_of_same_face {ℓ : ℕ}
    (forms : Finset (AffineForm ℓ)) (c : ℝ) {t t' : Fin ℓ → ℝ}
    (hface : SameAffineSignFace
      (thresholdSignForms (fun f : forms ↦ f.1) c) t t') :
    (∃ f ∈ forms, c ≤ |f.eval t|) ↔
      (∃ f ∈ forms, c ≤ |f.eval t'|) := by
  have h := affineMaxAbsGE_iff_of_same_threshold_face
    (fun f : forms ↦ f.1) c hface
  simp only [affineMaxAbsGE] at h
  constructor
  · rintro ⟨f, hf, hft⟩
    rcases h.mp ⟨⟨f, hf⟩, hft⟩ with ⟨g, hg⟩
    exact ⟨g.1, g.2, hg⟩
  · rintro ⟨f, hf, hft⟩
    rcases h.mpr ⟨⟨f, hf⟩, hft⟩ with ⟨g, hg⟩
    exact ⟨g.1, g.2, hg⟩

/-- The threshold comparison with `q` is equivalent to an existential
absolute-value threshold over the symbolic affine list. -/
theorem qSeminorm_ge_iff_exists_symbolicAffineQForm {ℓ : ℕ}
    (rowU rowV u v : RealL2) (A₀ B₀ : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (t : Fin ℓ → ℝ) (c : ℝ)
    (hrowU : ∀ n, n ∉ A₀ → rowU n = 0)
    (hrowV : ∀ n, n ∉ B₀ → rowV n = 0)
    (hu : ∀ n, u n =
      (labelledCoordinateForm (fun i ↦ rowU i) copy index .first n).eval t)
    (hv : ∀ n, v n =
      (labelledCoordinateForm (fun i ↦ rowV i) copy index .second n).eval t) :
    c ≤ qSeminorm (WithLp.toLp 2 (u, v)) ↔
      ∃ f ∈ symbolicAffineQForms (fun i ↦ rowU i) (fun i ↦ rowV i)
        A₀ B₀ copy index, c ≤ |f.eval t| := by
  rw [qSeminorm_eq_max_symbolicAffineQValues rowU rowV u v A₀ B₀
    copy index t hrowU hrowV hu hv]
  let forms := symbolicAffineQForms (fun i ↦ rowU i) (fun i ↦ rowV i)
    A₀ B₀ copy index
  let values := symbolicAffineQValues (fun i ↦ rowU i) (fun i ↦ rowV i)
    A₀ B₀ copy index t
  let hvalues := symbolicAffineQValues_nonempty (fun i ↦ rowU i) (fun i ↦ rowV i)
    A₀ B₀ copy index t
  constructor
  · intro hc
    have hmaxmem := Finset.max'_mem values hvalues
    dsimp [values, symbolicAffineQValues] at hmaxmem
    rcases Finset.mem_image.mp hmaxmem with ⟨f, hf, hfeval⟩
    refine ⟨f, hf, ?_⟩
    exact hc.trans_eq hfeval.symm
  · rintro ⟨f, hf, hcf⟩
    exact hcf.trans (Finset.le_max' values _ (by
      dsimp [values, symbolicAffineQValues]
      exact Finset.mem_image_of_mem _ hf))

/-- For one fixed symbolic row list, its threshold trace is constant on a
sign face of the two shifted copies. -/
theorem symbolicQThreshold_iff_of_same_face {ℓ : ℕ}
    (rowU rowV : ℕ → ℝ) (A₀ B₀ : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (c : ℝ) {t t' : Fin ℓ → ℝ}
    (hface : SameAffineSignFace
      (thresholdSignForms
        (fun f : symbolicAffineQForms rowU rowV A₀ B₀ copy index ↦ f.1) c)
      t t') :
    (∃ f ∈ symbolicAffineQForms rowU rowV A₀ B₀ copy index,
        c ≤ |f.eval t|) ↔
      (∃ f ∈ symbolicAffineQForms rowU rowV A₀ B₀ copy index,
        c ≤ |f.eval t'|) := by
  exact finset_abs_threshold_iff_of_same_face
    (symbolicAffineQForms rowU rowV A₀ B₀ copy index) c hface

/-- Consequently, two parameters in the same sign face give the same
threshold truth value for `q` on a fixed row. -/
theorem qSeminorm_threshold_iff_of_same_symbolic_face {ℓ : ℕ}
    (rowU rowV u v u' v' : RealL2) (A₀ B₀ : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (c : ℝ) {t t' : Fin ℓ → ℝ}
    (hrowU : ∀ n, n ∉ A₀ → rowU n = 0)
    (hrowV : ∀ n, n ∉ B₀ → rowV n = 0)
    (hu : ∀ n, u n =
      (labelledCoordinateForm (fun i ↦ rowU i) copy index .first n).eval t)
    (hv : ∀ n, v n =
      (labelledCoordinateForm (fun i ↦ rowV i) copy index .second n).eval t)
    (hu' : ∀ n, u' n =
      (labelledCoordinateForm (fun i ↦ rowU i) copy index .first n).eval t')
    (hv' : ∀ n, v' n =
      (labelledCoordinateForm (fun i ↦ rowV i) copy index .second n).eval t')
    (hface : SameAffineSignFace
      (thresholdSignForms
        (fun f : symbolicAffineQForms (fun i ↦ rowU i) (fun i ↦ rowV i)
          A₀ B₀ copy index ↦ f.1) c) t t') :
    (c ≤ qSeminorm (WithLp.toLp 2 (u, v)) ↔
      c ≤ qSeminorm (WithLp.toLp 2 (u', v'))) := by
  rw [qSeminorm_ge_iff_exists_symbolicAffineQForm rowU rowV u v A₀ B₀
      copy index t c hrowU hrowV hu hv,
    qSeminorm_ge_iff_exists_symbolicAffineQForm rowU rowV u' v' A₀ B₀
      copy index t' c hrowU hrowV hu' hv']
  exact symbolicQThreshold_iff_of_same_face
    (fun i ↦ rowU i) (fun i ↦ rowV i) A₀ B₀ copy index c hface

/-- The exact face-count expression used in the manuscript. -/
def hyperplaneFaceBound (N ℓ : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (ℓ + 1), 2 ^ j * N.choose j

@[simp]
theorem hyperplaneFaceBound_zero_dim (N : ℕ) : hyperplaneFaceBound N 0 = 1 := by
  simp [hyperplaneFaceBound]

/-- Adding one ambient dimension appends one binomial term. -/
theorem hyperplaneFaceBound_succ_dim (N ℓ : ℕ) :
    hyperplaneFaceBound N (ℓ + 1) =
      hyperplaneFaceBound N ℓ + 2 ^ (ℓ + 1) * N.choose (ℓ + 1) := by
  simp [hyperplaneFaceBound, Finset.sum_range_succ]

@[simp]
theorem hyperplaneFaceBound_zero_forms (ℓ : ℕ) : hyperplaneFaceBound 0 ℓ = 1 := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
      rw [hyperplaneFaceBound_succ_dim, ih]
      simp

/-- Pascal recurrence for the face bound. This is precisely the numerical
recurrence produced when a new hyperplane is inserted. -/
theorem hyperplaneFaceBound_succ_forms_succ_dim (N ℓ : ℕ) :
    hyperplaneFaceBound (N + 1) (ℓ + 1) =
      hyperplaneFaceBound N (ℓ + 1) + 2 * hyperplaneFaceBound N ℓ := by
  induction ℓ with
  | zero =>
      simp [hyperplaneFaceBound, Finset.sum_range_succ]
      omega
  | succ ℓ ih =>
      rw [hyperplaneFaceBound_succ_dim (N + 1) (ℓ + 1), ih,
        hyperplaneFaceBound_succ_dim N (ℓ + 1),
        hyperplaneFaceBound_succ_dim N ℓ, Nat.choose_succ_succ]
      ring

/-- Every summand in the face bound is controlled by the top-degree monomial
when `N` is positive. -/
theorem hyperplaneFaceBound_summand_le {N ℓ j : ℕ}
    (hN : 0 < N) (hj : j ≤ ℓ) :
    2 ^ j * N.choose j ≤ (2 * N) ^ ℓ := by
  calc
    2 ^ j * N.choose j ≤ 2 ^ j * N ^ j :=
      Nat.mul_le_mul_left _ (Nat.choose_le_pow N j)
    _ = (2 * N) ^ j := by rw [mul_pow]
    _ ≤ (2 * N) ^ ℓ := pow_le_pow_right' (by omega) hj

/-- The manuscript's coarse polynomial estimate for the exact face bound. -/
theorem hyperplaneFaceBound_le_polynomial {N ℓ : ℕ} (hN : 0 < N) :
    hyperplaneFaceBound N ℓ ≤ (ℓ + 1) * (2 * N) ^ ℓ := by
  unfold hyperplaneFaceBound
  calc
    _ ≤ ∑ _j ∈ Finset.range (ℓ + 1), (2 * N) ^ ℓ := by
      apply Finset.sum_le_sum
      intro j hj
      exact hyperplaneFaceBound_summand_le hN (by
        have := Finset.mem_range.mp hj
        omega)
    _ = (ℓ + 1) * (2 * N) ^ ℓ := by simp

end NormFormula.HalfGraph
