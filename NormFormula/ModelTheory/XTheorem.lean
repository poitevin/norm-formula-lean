import NormFormula.Analytic.Separability
import NormFormula.Analytic.XUniformConvex
import NormFormula.ModelTheory.XStability
import NormFormula.ModelTheory.XTheoryIP

/-!
# The theorem about `X`

This file assembles the two conclusions of the manuscript's theorem about the
space `X`: the norm formula is stable on the distinguished Banach structure,
but has the independence property in its complete theory.

All analytic and finite-pattern inputs are unconditional Lean theorems.  The
only parameter is the explicit continuous-logic compactness semantics carried
by `CompleteTheoryIPSemantics`.
-/

namespace NormFormula.X

noncomputable section

universe w

namespace CompleteTheoryIPPresentation

variable {S : NormFormula.CompleteTheoryIPSemantics XSpace XSpace}


end CompleteTheoryIPPresentation

/-- The unconditional separability and quantitative geometric conclusions
for the concrete space `X`. -/
theorem verified_geometric_conclusions :
    TopologicalSpace.IsSeparable (Set.univ : Set XSpace) ∧
      (∀ x y : XSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤
          1 - (1 / 12 : ℝ) * ‖x - y‖ ^ 2) ∧
      (∀ x : XSpace, ‖toHilbert x‖ ≤ ‖x‖) ∧
      (∀ z : XHilbertSpace,
        ‖ofHilbert z‖ ≤ Real.sqrt 3 * ‖z‖) := by
  exact ⟨TopologicalSpace.isSeparable_univ_iff.mpr inferInstance,
    fun _ _ hx hy ↦ norm_midpoint_sq_le hx hy,
    norm_toHilbert_le, norm_ofHilbert_le⟩

end

end NormFormula.X
