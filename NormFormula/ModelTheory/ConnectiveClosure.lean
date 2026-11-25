import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.SymmDiff
import NormFormula.ModelTheory.LocalNIP

/-!
# The finite-pattern connective interface

Mathlib does not currently provide the continuous-logic theorem that NIP is
closed under continuous connectives.  This module isolates the exact semantic
principle required here, without adding it as an axiom.  It also verifies the
analytic part for the particular Euclidean connective used to reconstruct the
`Y`-norm.
-/

namespace NormFormula


/-- The Euclidean connective used in the definition of every augmented norm. -/
noncomputable def euclideanConnective (a b : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 + b ^ 2)

/-- The Euclidean connective is the ordinary norm of the associated complex
number. -/
theorem euclideanConnective_eq_complex_norm (a b : ℝ) :
    euclideanConnective a b = ‖(⟨a, b⟩ : ℂ)‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  rfl

/-- Sharp Euclidean reverse-triangle estimate for the connective. -/
theorem abs_euclideanConnective_sub_le (a b c d : ℝ) :
    |euclideanConnective a b - euclideanConnective c d| ≤
      Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
  rw [euclideanConnective_eq_complex_norm,
    euclideanConnective_eq_complex_norm]
  calc
    |‖(⟨a, b⟩ : ℂ)‖ - ‖(⟨c, d⟩ : ℂ)‖| ≤
        ‖(⟨a, b⟩ : ℂ) - (⟨c, d⟩ : ℂ)‖ :=
      abs_norm_sub_norm_le _ _
    _ = Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
      rw [Complex.norm_eq_sqrt_sq_add_sq]
      rfl

/-- With the standard max metric on `ℝ × ℝ`, the Euclidean connective is
`√2`-Lipschitz. -/
theorem euclideanConnective_dist_le (p q : ℝ × ℝ) :
    dist (euclideanConnective p.1 p.2) (euclideanConnective q.1 q.2) ≤
      Real.sqrt 2 * dist p q := by
  let D := dist p q
  have hfirst : |p.1 - q.1| ≤ D := by
    dsimp [D]
    rw [Prod.dist_eq]
    simp [Real.dist_eq]
  have hsecond : |p.2 - q.2| ≤ D := by
    dsimp [D]
    rw [Prod.dist_eq]
    simp [Real.dist_eq]
  have hsquares : (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 ≤ 2 * D ^ 2 := by
    nlinarith [sq_le_sq₀ (abs_nonneg _) (dist_nonneg : 0 ≤ D) |>.2 hfirst,
      sq_le_sq₀ (abs_nonneg _) (dist_nonneg : 0 ≤ D) |>.2 hsecond,
      sq_abs (p.1 - q.1), sq_abs (p.2 - q.2)]
  have hroot := Real.sqrt_le_sqrt hsquares
  have hD : 0 ≤ D := dist_nonneg
  have hrhs : Real.sqrt (2 * D ^ 2) = Real.sqrt 2 * D := by
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ)), Real.sqrt_sq hD]
  rw [Real.dist_eq]
  exact (abs_euclideanConnective_sub_le p.1 p.2 q.1 q.2).trans
    (hroot.trans_eq hrhs)

/-- Consequently the Euclidean connective is uniformly continuous on its
whole domain. -/
theorem euclideanConnective_uniformContinuous :
    UniformContinuous fun p : ℝ × ℝ ↦ euclideanConnective p.1 p.2 := by
  let K : NNReal := ⟨Real.sqrt 2, Real.sqrt_nonneg _⟩
  apply (LipschitzWith.of_dist_le_mul (K := K) ?_).uniformContinuous
  intro p q
  simpa [K] using euclideanConnective_dist_le p q


end NormFormula
