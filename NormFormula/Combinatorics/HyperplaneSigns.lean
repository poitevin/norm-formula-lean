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


end NormFormula.HalfGraph
