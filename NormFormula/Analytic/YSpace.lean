import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Topology.UniformSpace.UniformEmbedding
import NormFormula.Analytic.HalfGraphSeminorm

/-!
# The renormed Hilbert space as a Mathlib normed space

The preceding files keep the original Hilbert norm and the new `Y`-norm on a
single type so that comparison calculations are transparent.  Here we wrap the
same vectors in a dedicated type and install the `Y`-norm as the actual norm.
-/

namespace NormFormula.HalfGraph

/-- The Hilbertian product equipped with the paper's `Y`-norm. -/
structure Y where
  toHilbert : HilbertSpace

namespace Y

/-- Forget the `Y`-norm and return to the underlying Hilbert space. -/
def equivHilbert : Y ≃ HilbertSpace where
  toFun := toHilbert
  invFun := Y.mk
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : AddCommGroup Y := equivHilbert.addCommGroup
noncomputable instance : Module ℝ Y := equivHilbert.module ℝ

noncomputable instance : Norm Y where
  norm y := yNorm y.toHilbert

@[simp]
theorem norm_def (y : Y) : ‖y‖ = yNorm y.toHilbert := rfl

@[ext]
theorem ext {x y : Y} (h : x.toHilbert = y.toHilbert) : x = y := by
  cases x
  cases y
  simp_all

@[simp]
theorem toHilbert_zero : (0 : Y).toHilbert = 0 := rfl

@[simp]
theorem toHilbert_add (x y : Y) : (x + y).toHilbert = x.toHilbert + y.toHilbert := rfl

@[simp]
theorem toHilbert_neg (x : Y) : (-x).toHilbert = -x.toHilbert := rfl

@[simp]
theorem toHilbert_smul (r : ℝ) (x : Y) : (r • x).toHilbert = r • x.toHilbert := rfl

/-- The minimal norm axioms, inherited from the augmented seminorm construction. -/
private noncomputable def normedSpaceCore : NormedSpace.Core ℝ Y where
  norm_nonneg x := augmentedNorm_nonneg qSeminorm x.toHilbert
  norm_smul r x := by
    change yNorm (r • x.toHilbert) = ‖r‖ * yNorm x.toHilbert
    exact augmentedNorm_smul qSeminorm r x.toHilbert
  norm_triangle x y := by
    change yNorm (x.toHilbert + y.toHilbert) ≤ yNorm x.toHilbert + yNorm y.toHilbert
    exact augmentedNorm_add_le qSeminorm x.toHilbert y.toHilbert
  norm_eq_zero_iff x := by
    change yNorm x.toHilbert = 0 ↔ x = 0
    constructor
    · intro hx
      apply ext
      exact (augmentedNorm_eq_zero qSeminorm x.toHilbert).mp hx
    · rintro rfl
      exact (augmentedNorm_eq_zero qSeminorm 0).mpr rfl

noncomputable instance : NormedAddCommGroup Y :=
  NormedAddCommGroup.ofCore normedSpaceCore

noncomputable instance : NormedSpace ℝ Y :=
  NormedSpace.ofCore normedSpaceCore

/-- The identity map from `Y` to its Hilbert model, as a linear equivalence. -/
def linearEquivHilbert : Y ≃ₗ[ℝ] HilbertSpace where
  toEquiv := equivHilbert
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem linearEquivHilbert_apply (y : Y) : linearEquivHilbert y = y.toHilbert := rfl

@[simp]
theorem linearEquivHilbert_symm_apply (z : HilbertSpace) :
    linearEquivHilbert.symm z = ⟨z⟩ := rfl

/-- One side of the equivalence of the `Y`-norm and Hilbert norm. -/
theorem hilbert_norm_le_norm (y : Y) : ‖y.toHilbert‖ ≤ ‖y‖ :=
  norm_le_yNorm y.toHilbert

/-- The other side of the equivalence of the `Y`-norm and Hilbert norm. -/
theorem norm_le_sqrtThree_mul_hilbert_norm (y : Y) :
    ‖y‖ ≤ Real.sqrt 3 * ‖y.toHilbert‖ :=
  yNorm_le_sqrtThree_mul_norm y.toHilbert

/-- The identity between the two normed models is a continuous linear equivalence. -/
noncomputable def continuousLinearEquivHilbert : Y ≃L[ℝ] HilbertSpace :=
  linearEquivHilbert.toContinuousLinearEquivOfBounds 1 (Real.sqrt 3)
    (fun y => by simpa using hilbert_norm_le_norm y)
    (fun z => by simpa using yNorm_le_sqrtThree_mul_norm z)

/-- `Y` is complete because its norm is equivalent to the complete Hilbert norm. -/
noncomputable instance : CompleteSpace Y :=
  (completeSpace_congr continuousLinearEquivHilbert.isUniformEmbedding).mpr inferInstance

/-- The paper's quantitative midpoint estimate, now expressed using the actual norm on `Y`. -/
theorem norm_midpoint_sq_le {x y : Y} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤
      1 - (1 / 12 : ℝ) * ‖x - y‖ ^ 2 := by
  change yNorm ((1 / 2 : ℝ) • (x.toHilbert + y.toHilbert)) ^ 2 ≤
    1 - (1 / 12 : ℝ) * yNorm (x.toHilbert - y.toHilbert) ^ 2
  exact yNorm_midpoint_sq_le hx hy

/-- The quantitative midpoint estimate supplies Mathlib's standard uniform-convexity interface. -/
noncomputable instance : UniformConvexSpace Y where
  uniform_convex {ε} hε := by
    let δ : ℝ := min 1 (ε ^ 2 / 12)
    have hδ : 0 < δ := by
      exact lt_min one_pos (div_pos (sq_pos_of_pos hε) (by norm_num))
    refine ⟨δ, hδ, ?_⟩
    intro x hx y hy hxy
    by_cases hεtwo : ε ≤ 2
    · have hmid := norm_midpoint_sq_le hx.le hy.le
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hmid
      have hsum_nonneg : 0 ≤ ‖x + y‖ := norm_nonneg _
      have hsum_le_two : ‖x + y‖ ≤ 2 := by
        calc
          ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
          _ = 2 := by rw [hx, hy]; norm_num
      have hdist_nonneg : 0 ≤ ‖x - y‖ := norm_nonneg _
      have heps_sq_le : ε ^ 2 ≤ ‖x - y‖ ^ 2 :=
        (sq_le_sq₀ hε.le hdist_nonneg).2 hxy
      have heps_sq_le_four : ε ^ 2 ≤ 4 := by
        nlinarith [sq_nonneg (2 - ε)]
      have htarget_nonneg : 0 ≤ 2 - ε ^ 2 / 12 := by nlinarith
      have hsquares : ‖x + y‖ ^ 2 ≤ (2 - ε ^ 2 / 12) ^ 2 := by
        nlinarith [sq_nonneg (ε ^ 2)]
      have hstrong : ‖x + y‖ ≤ 2 - ε ^ 2 / 12 :=
        (sq_le_sq₀ hsum_nonneg htarget_nonneg).mp hsquares
      have hδle : δ ≤ ε ^ 2 / 12 := min_le_right _ _
      linarith
    · have hdist_le_two : ‖x - y‖ ≤ 2 := by
        calc
          ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
          _ = 2 := by rw [hx, hy]; norm_num
      exact (hεtwo (hxy.trans hdist_le_two)).elim

end Y

end NormFormula.HalfGraph
