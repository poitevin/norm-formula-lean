import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FieldSimp
import NormFormula.Combinatorics.HyperplaneSigns

/-!
# Crossing faces and restricting to an affine hyperplane

This file supplies the geometric ingredients for the hyperplane-arrangement
insertion recurrence.  A line segment joining opposite sides of a new
hyperplane crosses it without leaving an old sign face.  A nonconstant affine
zero hyperplane in `ℝ^(ℓ+1)` is explicitly parametrized by `ℝ^ℓ`, and every
older affine form restricts to an affine form on that parameter space.
-/

namespace NormFormula.HalfGraph

/-- The affine combination `(1-r)x + r y` in coordinate form. -/
def affineLinePoint {ℓ : ℕ} (r : ℝ) (x y : Fin ℓ → ℝ) : Fin ℓ → ℝ :=
  fun i ↦ (1 - r) * x i + r * y i

/-- Affine forms evaluate affinely along line segments. -/
theorem AffineForm.eval_affineLinePoint {ℓ : ℕ} (f : AffineForm ℓ)
    (r : ℝ) (x y : Fin ℓ → ℝ) :
    f.eval (affineLinePoint r x y) =
      (1 - r) * f.eval x + r * f.eval y := by
  rw [AffineForm.eval, AffineForm.eval, AffineForm.eval]
  change f.constant +
      ∑ i, f.coeff i * ((1 - r) * x i + r * y i) = _
  calc
    _ = f.constant +
        ((1 - r) * (∑ i, f.coeff i * x i) +
          r * (∑ i, f.coeff i * y i)) := by
      congr 1
      calc
        _ = ∑ i, ((1 - r) * (f.coeff i * x i) +
            r * (f.coeff i * y i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (1 - r) * (f.constant + ∑ i, f.coeff i * x i) +
        r * (f.constant + ∑ i, f.coeff i * y i) := by ring

/-- If a new affine form has opposite strict signs at two points in one old
face, its zero hyperplane meets that same old face. -/
theorem exists_zero_in_same_affineSignFace
    {ι : Type*} {ℓ : ℕ} (old : ι → AffineForm ℓ) (g : AffineForm ℓ)
    {x y : Fin ℓ → ℝ}
    (hface : SameAffineSignFace old x y)
    (hx : g.eval x < 0) (hy : 0 < g.eval y) :
    ∃ z, SameAffineSignFace old x z ∧ g.eval z = 0 := by
  let r : ℝ := -g.eval x / (g.eval y - g.eval x)
  have hden : 0 < g.eval y - g.eval x := by linarith
  have hrpos : 0 < r := by
    dsimp [r]
    exact div_pos (by linarith) hden
  have hrlt : r < 1 := by
    dsimp [r]
    rw [div_lt_one hden]
    linarith
  refine ⟨affineLinePoint r x y, ?_, ?_⟩
  · apply funext
    intro i
    have hi := congrFun hface i
    rcases lt_trichotomy ((old i).eval x) 0 with hix | hix | hix
    · have hiy : (old i).eval y < 0 := by
        apply sign_eq_neg_one_iff.mp
        exact hi.symm.trans (sign_neg hix)
      have hiz : (old i).eval (affineLinePoint r x y) < 0 := by
        rw [AffineForm.eval_affineLinePoint]
        nlinarith
      rw [affineSignProfile, affineSignProfile, sign_neg hix, sign_neg hiz]
    · have hiy : (old i).eval y = 0 := by
        apply sign_eq_zero_iff.mp
        exact hi.symm.trans (sign_eq_zero_iff.mpr hix)
      have hiz : (old i).eval (affineLinePoint r x y) = 0 := by
        rw [AffineForm.eval_affineLinePoint, hix, hiy]
        ring
      rw [affineSignProfile, affineSignProfile, hix, hiz, sign_zero]
    · have hiy : 0 < (old i).eval y := by
        apply sign_eq_one_iff.mp
        exact hi.symm.trans (sign_pos hix)
      have hiz : 0 < (old i).eval (affineLinePoint r x y) := by
        rw [AffineForm.eval_affineLinePoint]
        nlinarith
      rw [affineSignProfile, affineSignProfile, sign_pos hix, sign_pos hiz]
  · rw [AffineForm.eval_affineLinePoint]
    dsimp [r]
    field_simp [ne_of_gt hden]
    ring

/-- Solve the `k`th coordinate of `g=0` in terms of all remaining
coordinates. -/
noncomputable def hyperplaneSolvedCoordinate {ℓ : ℕ} (g : AffineForm (ℓ + 1))
    (k : Fin (ℓ + 1)) (x : Fin ℓ → ℝ) : ℝ :=
  -(g.constant + ∑ j, g.coeff (k.succAbove j) * x j) / g.coeff k

/-- Parametrize the zero hyperplane of `g` by inserting the solved coordinate
at a position where the linear coefficient is nonzero. -/
noncomputable def hyperplaneParam {ℓ : ℕ} (g : AffineForm (ℓ + 1))
    (k : Fin (ℓ + 1)) (x : Fin ℓ → ℝ) : Fin (ℓ + 1) → ℝ :=
  k.insertNth (hyperplaneSolvedCoordinate g k x) x

@[simp]
theorem hyperplaneParam_apply_pivot {ℓ : ℕ} (g : AffineForm (ℓ + 1))
    (k : Fin (ℓ + 1)) (x : Fin ℓ → ℝ) :
    hyperplaneParam g k x k = hyperplaneSolvedCoordinate g k x := by
  simp [hyperplaneParam]

@[simp]
theorem hyperplaneParam_apply_succAbove {ℓ : ℕ} (g : AffineForm (ℓ + 1))
    (k : Fin (ℓ + 1)) (x : Fin ℓ → ℝ) (j : Fin ℓ) :
    hyperplaneParam g k x (k.succAbove j) = x j := by
  simp [hyperplaneParam]

/-- Every point produced by `hyperplaneParam` lies on `g=0`. -/
theorem AffineForm.eval_hyperplaneParam_eq_zero {ℓ : ℕ}
    (g : AffineForm (ℓ + 1)) (k : Fin (ℓ + 1)) (hk : g.coeff k ≠ 0)
    (x : Fin ℓ → ℝ) :
    g.eval (hyperplaneParam g k x) = 0 := by
  rw [AffineForm.eval, Fin.sum_univ_succAbove (fun i ↦
    g.coeff i * hyperplaneParam g k x i) k]
  simp only [hyperplaneParam_apply_pivot, hyperplaneParam_apply_succAbove]
  unfold hyperplaneSolvedCoordinate
  field_simp [hk]
  ring

/-- Conversely, every point of `g=0` is produced by the parametrization. -/
theorem hyperplaneParam_surjective_on_zero {ℓ : ℕ}
    (g : AffineForm (ℓ + 1)) (k : Fin (ℓ + 1)) (hk : g.coeff k ≠ 0)
    {t : Fin (ℓ + 1) → ℝ} (ht : g.eval t = 0) :
    hyperplaneParam g k (fun j ↦ t (k.succAbove j)) = t := by
  rw [hyperplaneParam, Fin.insertNth_eq_iff]
  constructor
  · unfold hyperplaneSolvedCoordinate
    rw [AffineForm.eval, Fin.sum_univ_succAbove (fun i ↦ g.coeff i * t i) k] at ht
    field_simp [hk]
    field_simp [hk] at ht
    linarith
  · rfl

/-- Restrict an affine form `f` to the parametrized zero hyperplane of `g`. -/
noncomputable def AffineForm.restrictToZero {ℓ : ℕ}
    (f g : AffineForm (ℓ + 1)) (k : Fin (ℓ + 1)) : AffineForm ℓ where
  constant := f.constant - f.coeff k * g.constant / g.coeff k
  coeff j := f.coeff (k.succAbove j) -
    f.coeff k * g.coeff (k.succAbove j) / g.coeff k

/-- Evaluation of the restricted form agrees with evaluation upstairs. -/
theorem AffineForm.eval_restrictToZero {ℓ : ℕ}
    (f g : AffineForm (ℓ + 1)) (k : Fin (ℓ + 1)) (hk : g.coeff k ≠ 0)
    (x : Fin ℓ → ℝ) :
    (f.restrictToZero g k).eval x = f.eval (hyperplaneParam g k x) := by
  rw [AffineForm.eval, AffineForm.eval,
    Fin.sum_univ_succAbove (fun i ↦ f.coeff i * hyperplaneParam g k x i) k]
  simp only [AffineForm.restrictToZero, hyperplaneParam_apply_pivot,
    hyperplaneParam_apply_succAbove]
  have hsum :
      (∑ j, (f.coeff (k.succAbove j) -
          f.coeff k * g.coeff (k.succAbove j) / g.coeff k) * x j) =
        (∑ j, f.coeff (k.succAbove j) * x j) -
          (f.coeff k / g.coeff k) *
            (∑ j, g.coeff (k.succAbove j) * x j) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    field_simp [hk]
  rw [hsum]
  unfold hyperplaneSolvedCoordinate
  field_simp [hk]
  ring

/-- Old sign patterns realizable on the zero hyperplane of `g`. -/
noncomputable def zeroSliceSignPatterns
    {ι : Type*} [Fintype ι] {ℓ : ℕ}
    (old : ι → AffineForm ℓ) (g : AffineForm ℓ) : Finset (ι → SignType) := by
  classical
  exact Finset.univ.filter fun s ↦
    ∃ t, g.eval t = 0 ∧ affineSignProfile old t = s

@[simp]
theorem mem_zeroSliceSignPatterns
    {ι : Type*} [Fintype ι] {ℓ : ℕ}
    (old : ι → AffineForm ℓ) (g : AffineForm ℓ) (s : ι → SignType) :
    s ∈ zeroSliceSignPatterns old g ↔
      ∃ t, g.eval t = 0 ∧ affineSignProfile old t = s := by
  classical
  simp [zeroSliceSignPatterns]

/-- For a nonconstant `g`, its zero-slice sign patterns are exactly the
ordinary sign patterns of the restricted arrangement in one lower dimension. -/
theorem zeroSliceSignPatterns_eq_restricted
    {ι : Type*} [Fintype ι] {ℓ : ℕ}
    (old : ι → AffineForm (ℓ + 1)) (g : AffineForm (ℓ + 1))
    (k : Fin (ℓ + 1)) (hk : g.coeff k ≠ 0) :
    zeroSliceSignPatterns old g =
      realizableAffineSignPatterns (fun i ↦ (old i).restrictToZero g k) := by
  classical
  ext s
  rw [mem_zeroSliceSignPatterns, mem_realizableAffineSignPatterns]
  constructor
  · rintro ⟨t, hgt, rfl⟩
    let x : Fin ℓ → ℝ := fun j ↦ t (k.succAbove j)
    refine ⟨x, ?_⟩
    apply funext
    intro i
    simp only [affineSignProfile]
    rw [AffineForm.eval_restrictToZero (old i) g k hk]
    rw [hyperplaneParam_surjective_on_zero g k hk hgt]
  · rintro ⟨x, rfl⟩
    refine ⟨hyperplaneParam g k x, g.eval_hyperplaneParam_eq_zero k hk x, ?_⟩
    apply funext
    intro i
    simp only [affineSignProfile]
    rw [AffineForm.eval_restrictToZero (old i) g k hk]

end NormFormula.HalfGraph
