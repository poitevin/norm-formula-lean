import NormFormula.Analytic.Separability
import NormFormula.Examples.YInstability
import NormFormula.ModelTheory.YTheoryNIP

/-!
# The theorem about `Y`

This module assembles the previously verified components: the norm formula is
unstable on the distinguished space and NIP in its complete theory, while
`Y` is separable, uniformly convex with the stated midpoint estimate, and
`√3`-isomorphic to its Hilbert model.
-/

namespace NormFormula.HalfGraph.Y

noncomputable section

universe w z

namespace CompleteTheoryPresentation

variable {S : NormFormula.ContinuousNIPSemantics Y Y}

/-- The logical conclusions of the paper's theorem about `Y`. -/
theorem normFormula_unstableInY_and_isNIPInCompleteTheory
    (P : CompleteTheoryPresentation S) :
    (¬ NormFormula.IsStableOnBounded (S.reductValue P.normFormula)) ∧
      S.IsNIPInReduct P.normFormula := by
  constructor
  · intro hstable
    exact normPredicateTranslate_not_isStableOnBounded
      (hstable.congr P.normFormula_value)
  · exact P.normFormula_isNIPInCompleteTheory

end CompleteTheoryPresentation

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
