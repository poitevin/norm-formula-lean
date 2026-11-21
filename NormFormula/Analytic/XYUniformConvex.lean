import NormFormula.Analytic.XUniformConvex
import NormFormula.Analytic.XYSpace

/-!
# Uniform convexity of `X ⊕₂ Y`

The homogeneous augmented-norm midpoint estimate is first specialized to
each factor. Because it is written with the average of the two squared norms,
the two coordinate inequalities add exactly under the ℓ₂-product norm. This
gives the same constant `1 / 12` as for each factor and supplies Mathlib's
`UniformConvexSpace` interface for the concrete direct sum.
-/

namespace NormFormula.XY

noncomputable section

/-- The homogeneous midpoint estimate for the `X` factor. -/
private theorem xNorm_midpoint_sq_le_average_sub
    (x y : X.XSpace) :
    ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤
      (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 -
        (1 / 12 : ℝ) * ‖x - y‖ ^ 2 := by
  simp_rw [X.norm_eq_augmentedNorm_toHilbert]
  change NormFormula.augmentedNorm X.sumSeminorm
      ((1 / 2 : ℝ) • (X.toHilbert x + X.toHilbert y)) ^ 2 ≤
    (NormFormula.augmentedNorm X.sumSeminorm (X.toHilbert x) ^ 2 +
      NormFormula.augmentedNorm X.sumSeminorm (X.toHilbert y) ^ 2) / 2 -
      (1 / 12 : ℝ) *
        NormFormula.augmentedNorm X.sumSeminorm
          (X.toHilbert x - X.toHilbert y) ^ 2
  exact NormFormula.augmentedNorm_midpoint_sq_le_average_sub
    X.sumSeminorm X.sumSeminorm_sq_le_two_mul_norm_sq
    (X.toHilbert x) (X.toHilbert y)

/-- The homogeneous midpoint estimate for the `Y` factor. -/
private theorem yNorm_midpoint_sq_le_average_sub
    (x y : HalfGraph.Y) :
    ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤
      (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 -
        (1 / 12 : ℝ) * ‖x - y‖ ^ 2 := by
  change HalfGraph.yNorm
      ((1 / 2 : ℝ) • (x.toHilbert + y.toHilbert)) ^ 2 ≤
    (HalfGraph.yNorm x.toHilbert ^ 2 +
      HalfGraph.yNorm y.toHilbert ^ 2) / 2 -
      (1 / 12 : ℝ) *
        HalfGraph.yNorm (x.toHilbert - y.toHilbert) ^ 2
  exact NormFormula.augmentedNorm_midpoint_sq_le_average_sub
    HalfGraph.qSeminorm HalfGraph.qSeminorm_sq_le_two_mul_norm_sq
    x.toHilbert y.toHilbert

/-- The averaged midpoint estimate on the actual direct sum. -/
theorem norm_midpoint_sq_le_average_sub (x y : XYSpace) :
    ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤
      (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 -
        (1 / 12 : ℝ) * ‖x - y‖ ^ 2 := by
  have hx := xNorm_midpoint_sq_le_average_sub x.fst y.fst
  have hy := yNorm_midpoint_sq_le_average_sub x.snd y.snd
  simp only [WithLp.prod_norm_sq_eq_of_L2, WithLp.smul_fst, WithLp.smul_snd,
    WithLp.add_fst, WithLp.add_snd, WithLp.sub_fst, WithLp.sub_snd]
  nlinarith

/-- The paper's unit-ball midpoint estimate for `X ⊕₂ Y`. -/
theorem norm_midpoint_sq_le {x y : XYSpace}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤
      1 - (1 / 12 : ℝ) * ‖x - y‖ ^ 2 := by
  have hxSq : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hySq : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y]
  exact (norm_midpoint_sq_le_average_sub x y).trans (by linarith)

/-- The explicit midpoint estimate supplies uniform convexity of the direct sum. -/
noncomputable instance : UniformConvexSpace XYSpace where
  uniform_convex {ε} hε := by
    let δ : ℝ := min 1 (ε ^ 2 / 12)
    have hδ : 0 < δ := by
      exact lt_min one_pos (div_pos (sq_pos_of_pos hε) (by norm_num))
    refine ⟨δ, hδ, ?_⟩
    intro x hx y hy hxy
    by_cases hεtwo : ε ≤ 2
    · have hmid := norm_midpoint_sq_le hx.le hy.le
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hmid
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

end

end NormFormula.XY
