import NormFormula.Analytic.Separability
import NormFormula.Examples.YInstability

/-! Separability and quantitative norm geometry of `Y`. -/

namespace NormFormula.HalfGraph.Y

noncomputable section

/-- The unconditional separability and quantitative geometric conclusions
for the concrete space `Y`. -/
theorem verified_geometric_conclusions :
    TopologicalSpace.IsSeparable (Set.univ : Set Y) ∧
      (∀ x y : Y, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤
          1 - (1 / 12 : ℝ) * ‖x - y‖ ^ 2) ∧
      (∀ y : Y, ‖y.toHilbert‖ ≤ ‖y‖) ∧
      (∀ z : HilbertSpace,
        ‖linearEquivHilbert.symm z‖ ≤ Real.sqrt 3 * ‖z‖) := by
  refine ⟨TopologicalSpace.isSeparable_univ_iff.mpr inferInstance,
    ?_, hilbert_norm_le_norm, ?_⟩
  · intro x y hx hy
    exact norm_midpoint_sq_le hx hy
  · intro z
    simpa using norm_le_sqrtThree_mul_hilbert_norm
      (linearEquivHilbert.symm z)

end

end NormFormula.HalfGraph.Y
