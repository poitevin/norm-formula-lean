import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Seminorm
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A Hilbert norm augmented by a seminorm

This file formalizes the analytic construction used repeatedly in the paper.
Given a real inner-product space and a seminorm `M`, its augmented norm is

`sqrt (‖x‖ ^ 2 + M x ^ 2)`.

The first results expose the square of this quantity and prove the norm
comparison that follows from `M x ^ 2 ≤ 2 * ‖x‖ ^ 2`.
-/

namespace NormFormula

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Hilbert norm augmented in quadrature by a seminorm. -/
noncomputable def augmentedNorm (M : Seminorm ℝ E) (x : E) : ℝ :=
  Real.sqrt (‖x‖ ^ 2 + M x ^ 2)

theorem augmentedNorm_nonneg (M : Seminorm ℝ E) (x : E) :
    0 ≤ augmentedNorm M x := by
  exact Real.sqrt_nonneg _

/-- Squaring the augmented norm recovers its defining sum. -/
@[simp]
theorem augmentedNorm_sq (M : Seminorm ℝ E) (x : E) :
    augmentedNorm M x ^ 2 = ‖x‖ ^ 2 + M x ^ 2 := by
  rw [augmentedNorm, Real.sq_sqrt]
  positivity

/-- The original Hilbert norm is bounded by the augmented norm. -/
theorem norm_le_augmentedNorm (M : Seminorm ℝ E) (x : E) :
    ‖x‖ ≤ augmentedNorm M x := by
  apply Real.le_sqrt_of_sq_le
  exact le_add_of_nonneg_right (sq_nonneg (M x))

/-- The adjoining seminorm is also bounded by the augmented norm. -/
theorem seminorm_le_augmentedNorm (M : Seminorm ℝ E) (x : E) :
    M x ≤ augmentedNorm M x := by
  apply Real.le_sqrt_of_sq_le
  exact le_add_of_nonneg_left (sq_nonneg ‖x‖)

/-- The augmented norm is absolutely homogeneous. -/
theorem augmentedNorm_smul (M : Seminorm ℝ E) (r : ℝ) (x : E) :
    augmentedNorm M (r • x) = ‖r‖ * augmentedNorm M x := by
  have hleft : 0 ≤ augmentedNorm M (r • x) := augmentedNorm_nonneg M _
  have hright : 0 ≤ ‖r‖ * augmentedNorm M x :=
    mul_nonneg (norm_nonneg _) (augmentedNorm_nonneg M _)
  have hsquares : augmentedNorm M (r • x) ^ 2 = (‖r‖ * augmentedNorm M x) ^ 2 := by
    rw [augmentedNorm_sq, mul_pow, augmentedNorm_sq, norm_smul, map_smul_eq_mul]
    ring
  nlinarith

/-- The two-dimensional Euclidean triangle inequality, specialized to nonnegative coordinates. -/
private theorem sqrt_sq_add_sq_add_le
    (a b c d : ℝ) :
    Real.sqrt ((a + c) ^ 2 + (b + d) ^ 2) ≤
      Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt (c ^ 2 + d ^ 2) := by
  calc
    Real.sqrt ((a + c) ^ 2 + (b + d) ^ 2) = ‖(⟨a + c, b + d⟩ : ℂ)‖ := by
      rw [Complex.norm_eq_sqrt_sq_add_sq]
    _ = ‖(⟨a, b⟩ : ℂ) + (⟨c, d⟩ : ℂ)‖ := by rfl
    _ ≤ ‖(⟨a, b⟩ : ℂ)‖ + ‖(⟨c, d⟩ : ℂ)‖ := norm_add_le _ _
    _ = Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt (c ^ 2 + d ^ 2) := by
      rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]

/-- Triangle inequality for the augmented norm. -/
theorem augmentedNorm_add_le (M : Seminorm ℝ E) (x y : E) :
    augmentedNorm M (x + y) ≤ augmentedNorm M x + augmentedNorm M y := by
  have hnorm : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have hseminorm : M (x + y) ≤ M x + M y := map_add_le_add M x y
  have hnorm_nonneg : 0 ≤ ‖x + y‖ := norm_nonneg _
  have hseminorm_nonneg : 0 ≤ M (x + y) := by positivity
  have hxnorm_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
  have hynorm_nonneg : 0 ≤ ‖y‖ := norm_nonneg _
  have hxseminorm_nonneg : 0 ≤ M x := by positivity
  have hyseminorm_nonneg : 0 ≤ M y := by positivity
  rw [augmentedNorm, augmentedNorm, augmentedNorm]
  calc
    Real.sqrt (‖x + y‖ ^ 2 + M (x + y) ^ 2) ≤
        Real.sqrt ((‖x‖ + ‖y‖) ^ 2 + (M x + M y) ^ 2) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    _ ≤ Real.sqrt (‖x‖ ^ 2 + M x ^ 2) + Real.sqrt (‖y‖ ^ 2 + M y ^ 2) :=
      sqrt_sq_add_sq_add_le ‖x‖ (M x) ‖y‖ (M y)

/-- The augmented norm vanishes exactly at zero. -/
@[simp]
theorem augmentedNorm_eq_zero (M : Seminorm ℝ E) (x : E) :
    augmentedNorm M x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    exact norm_eq_zero.mp (le_antisymm ((norm_le_augmentedNorm M x).trans_eq hx) (norm_nonneg _))
  · rintro rfl
    simp [augmentedNorm]

/-- The augmented norm, bundled as a Mathlib seminorm. It is positive definite by
`augmentedNorm_eq_zero`; the seminorm bundle is useful for taking later suprema. -/
noncomputable def augmentedSeminorm (M : Seminorm ℝ E) : Seminorm ℝ E :=
  Seminorm.of (augmentedNorm M) (augmentedNorm_add_le M) (augmentedNorm_smul M)

@[simp]
theorem augmentedSeminorm_apply (M : Seminorm ℝ E) (x : E) :
    augmentedSeminorm M x = augmentedNorm M x := rfl

/-- Squared upper comparison used in the paper. -/
theorem augmentedNorm_sq_le_three_mul
    (M : Seminorm ℝ E) (hM : ∀ z, M z ^ 2 ≤ 2 * ‖z‖ ^ 2) (x : E) :
    augmentedNorm M x ^ 2 ≤ 3 * ‖x‖ ^ 2 := by
  rw [augmentedNorm_sq]
  linarith [hM x]

/-- If `M² ≤ 2‖·‖²`, the augmented norm is at most `sqrt 3` times the Hilbert norm. -/
theorem augmentedNorm_le_sqrtThree_mul
    (M : Seminorm ℝ E) (hM : ∀ z, M z ^ 2 ≤ 2 * ‖z‖ ^ 2) (x : E) :
    augmentedNorm M x ≤ Real.sqrt 3 * ‖x‖ := by
  have hsqrt : 0 ≤ Real.sqrt 3 * ‖x‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  rw [augmentedNorm, Real.sqrt_le_iff]
  constructor
  · exact hsqrt
  · rw [mul_pow, Real.sq_sqrt (by norm_num)]
    linarith [hM x]

/-- Convexity of a seminorm, in the squared midpoint form used by the proof. -/
theorem seminorm_midpoint_sq_le (M : Seminorm ℝ E) (x y : E) :
    M ((1 / 2 : ℝ) • (x + y)) ^ 2 ≤ (M x ^ 2 + M y ^ 2) / 2 := by
  have hmid : M ((1 / 2 : ℝ) • (x + y)) ≤ (M x + M y) / 2 := by
    calc
      M ((1 / 2 : ℝ) • (x + y)) = (1 / 2 : ℝ) * M (x + y) := by
        rw [map_smul_eq_mul]
        norm_num
      _ ≤ (1 / 2 : ℝ) * (M x + M y) :=
        mul_le_mul_of_nonneg_left (map_add_le_add M x y) (by norm_num)
      _ = (M x + M y) / 2 := by ring
  have hmid_nonneg : 0 ≤ M ((1 / 2 : ℝ) • (x + y)) := by positivity
  have hx_nonneg : 0 ≤ M x := by positivity
  have hy_nonneg : 0 ≤ M y := by positivity
  nlinarith [sq_nonneg (M x - M y)]

/-- The Hilbert-space midpoint identity, arranged for the augmented-norm proof. -/
theorem norm_midpoint_sq_eq (x y : E) :
    ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 =
      (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 - ‖x - y‖ ^ 2 / 4 := by
  have hpar := parallelogram_law_with_norm ℝ x y
  rw [norm_smul]
  norm_num
  nlinarith

/-- The homogeneous midpoint estimate underlying the paper's unit-ball
formulation. This stronger averaged form is what makes the estimate add
exactly under ℓ₂-products. -/
theorem augmentedNorm_midpoint_sq_le_average_sub
    (M : Seminorm ℝ E) (hM : ∀ z, M z ^ 2 ≤ 2 * ‖z‖ ^ 2)
    (x y : E) :
    augmentedNorm M ((1 / 2 : ℝ) • (x + y)) ^ 2 ≤
      (augmentedNorm M x ^ 2 + augmentedNorm M y ^ 2) / 2 -
        (1 / 12 : ℝ) * augmentedNorm M (x - y) ^ 2 := by
  have hmid_hilbert := norm_midpoint_sq_eq x y
  have hmid_seminorm := seminorm_midpoint_sq_le M x y
  have hdiff := augmentedNorm_sq_le_three_mul M hM (x - y)
  simp only [augmentedNorm_sq] at hdiff ⊢
  nlinarith

/-- The quantitative midpoint estimate in the paper's augmented-norm lemma. -/
theorem augmentedNorm_midpoint_sq_le
    (M : Seminorm ℝ E) (hM : ∀ z, M z ^ 2 ≤ 2 * ‖z‖ ^ 2)
    {x y : E} (hx : augmentedNorm M x ≤ 1) (hy : augmentedNorm M y ≤ 1) :
    augmentedNorm M ((1 / 2 : ℝ) • (x + y)) ^ 2 ≤
      1 - (1 / 12 : ℝ) * augmentedNorm M (x - y) ^ 2 := by
  have hx_sq : augmentedNorm M x ^ 2 ≤ 1 := by
    nlinarith [augmentedNorm_nonneg M x]
  have hy_sq : augmentedNorm M y ^ 2 ≤ 1 := by
    nlinarith [augmentedNorm_nonneg M y]
  exact (augmentedNorm_midpoint_sq_le_average_sub M hM x y).trans (by
    linarith)

end NormFormula
