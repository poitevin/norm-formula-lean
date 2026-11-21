import NormFormula.Analytic.HilbertNoC0
import NormFormula.ContinuousLogic.XHilbertBallSmallSort

/-!
# Final geometry of the separable Hilbertian norm-addition model

This file attaches the geometric conclusions derived from the complete typed
X ball theory to `SeparableHilbertianNormAddIPModel`.  In particular, the
midpoint estimate and uniform convexity are no longer presentation fields:
they follow from exact global unit-sort coverage.  The exclusion of `c₀`
follows from the reconstructed auxiliary Hilbert equivalence.
-/

namespace NormFormula.X.BallLanguage

noncomputable section

open TopologicalSpace

namespace SeparableHilbertianNormAddIPModel

/-- The paper's Hilbert comparison, oriented from the reconstructed Banach
carrier to its auxiliary Hilbert carrier. -/
def continuousLinearEquivHilbert
    (M : SeparableHilbertianNormAddIPModel) :
    M.model.CompletedDirectedPoint ≃L[ℝ]
      M.model.AuxiliaryHilbertCarrier :=
  M.model.auxiliaryHilbertContinuousLinearEquiv.symm

/-- The auxiliary Hilbert norm is bounded above by the reconstructed Banach
norm with constant one. -/
theorem norm_continuousLinearEquivHilbert_le
    (M : SeparableHilbertianNormAddIPModel)
    (x : M.model.CompletedDirectedPoint) :
    ‖M.continuousLinearEquivHilbert x‖ ≤ ‖x‖ := by
  have h := M.model.norm_auxiliaryHilbertCarrier_le_original
    (M.continuousLinearEquivHilbert x)
  calc
    ‖M.continuousLinearEquivHilbert x‖ ≤
        ‖(M.continuousLinearEquivHilbert x).toCompletedDirectedPoint‖ := h
    _ = ‖x‖ := by
      change ‖M.model.auxiliaryHilbertContinuousLinearEquiv
        (M.model.auxiliaryHilbertContinuousLinearEquiv.symm x)‖ = ‖x‖
      rw [ContinuousLinearEquiv.apply_symm_apply]

/-- The inverse Hilbert comparison has the paper's exact constant `√3`. -/
theorem norm_continuousLinearEquivHilbert_symm_le
    (M : SeparableHilbertianNormAddIPModel)
    (h : M.model.AuxiliaryHilbertCarrier) :
    ‖M.continuousLinearEquivHilbert.symm h‖ ≤
      Real.sqrt 3 * ‖h‖ := by
  change ‖M.model.auxiliaryHilbertContinuousLinearEquiv h‖ ≤
    Real.sqrt 3 * ‖h‖
  exact M.model.original_norm_le_sqrtThree_mul_auxiliaryHilbertCarrier h

/-- The precise quantitative meaning of the paper's assertion that the
extracted Banach space is `√3`-isomorphic to Hilbert space. -/
def IsSqrtThreeIsomorphicToHilbert
    (M : SeparableHilbertianNormAddIPModel) : Prop :=
  (∀ x : M.model.CompletedDirectedPoint,
      ‖M.continuousLinearEquivHilbert x‖ ≤ ‖x‖) ∧
    ∀ h : M.model.AuxiliaryHilbertCarrier,
      ‖M.continuousLinearEquivHilbert.symm h‖ ≤
        Real.sqrt 3 * ‖h‖

theorem isSqrtThreeIsomorphicToHilbert
    (M : SeparableHilbertianNormAddIPModel) :
    M.IsSqrtThreeIsomorphicToHilbert :=
  ⟨M.norm_continuousLinearEquivHilbert_le,
    M.norm_continuousLinearEquivHilbert_symm_le⟩

/-- The global transferred midpoint estimate on the public model package. -/
theorem norm_midpoint_sq_le
    (M : SeparableHilbertianNormAddIPModel)
    (x y : M.model.CompletedDirectedPoint)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤
      1 - (1 / 12 : ℝ) * ‖x - y‖ ^ 2 :=
  midpoint_completedNorm M.model x y hx hy

/-- Uniform convexity of the public reconstructed Banach model, derived from
the transferred midpoint sentence rather than stored in the package. -/
@[reducible] def uniformConvexSpace
    (M : SeparableHilbertianNormAddIPModel) :
    UniformConvexSpace M.model.CompletedDirectedPoint :=
  completedDirectedPointUniformConvexSpace M.model

/-- The reconstructed Banach model contains no isomorphic copy of `c₀`.
This direct Hilbert-space proof avoids a separate Milman--Pettis dependency. -/
theorem not_containsIsomorphicCopyOfC0
    (M : SeparableHilbertianNormAddIPModel) :
    ¬ NormFormula.ContainsIsomorphicCopyOfC0
      M.model.CompletedDirectedPoint := by
  exact NormFormula.not_containsIsomorphicCopyOfC0_of_equiv_innerProduct
    M.continuousLinearEquivHilbert (Real.sqrt 3)
    (Real.sqrt_pos.2 (by norm_num))
    M.norm_continuousLinearEquivHilbert_symm_le

/-- Assumption-free final assembly for the public separable Hilbertian IP
model.  Every geometric component is constructed from `model`; only
separability and the retained norm-addition witness are stored fields. -/
theorem has_all_geometric_conclusions
    (M : SeparableHilbertianNormAddIPModel) :
    SeparableSpace M.model.CompletedDirectedPoint ∧
      SeparableSpace M.model.AuxiliaryHilbertCarrier ∧
      M.model.HasCompletedNormAddWitness
        4 (Real.sqrt 3) (Real.sqrt 6) ∧
      (∀ x y : M.model.CompletedDirectedPoint,
        ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤
            1 - (1 / 12 : ℝ) * ‖x - y‖ ^ 2) ∧
      UniformConvexSpace M.model.CompletedDirectedPoint ∧
      M.IsSqrtThreeIsomorphicToHilbert ∧
      ¬ NormFormula.ContainsIsomorphicCopyOfC0
        M.model.CompletedDirectedPoint := by
  exact ⟨M.completedSeparable, M.auxiliaryHilbertSeparable,
    M.normAddWitness, M.norm_midpoint_sq_le, M.uniformConvexSpace,
    M.isSqrtThreeIsomorphicToHilbert,
    M.not_containsIsomorphicCopyOfC0⟩

end SeparableHilbertianNormAddIPModel

end

end NormFormula.X.BallLanguage
