import NormFormula.Analytic.HilbertNoC0
import NormFormula.Analytic.MidpointUniformConvex
import NormFormula.ContinuousLogic.XHilbertBallLimitTransfer

/-!
# Geometry of the one-sorted closed-span reduct

The reduct is a closed real subspace of `XSpace`, so its norm and linear
operations are inherited.  The paper's exact midpoint estimate therefore
restricts to the reduct and supplies an actual uniform-convexity structure.
Together with the restricted Hilbert equivalence, this also excludes an
isomorphic copy of `c₀`.
-/

namespace NormFormula.X.BallLanguage

noncomputable section

open NormFormula.ContinuousLogic

/-- The one-sorted reduct satisfies the paper's exact quadratic midpoint
estimate with constant `1/12`. -/
theorem limitBanachSpace_norm_midpoint_sq_le
    (initial : BallWitnessIndexing expansionStructure)
    (x y : LimitBanachSpace initial) (
      hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤
      1 - (1 / 12 : ℝ) * ‖x - y‖ ^ 2 := by
  change ‖(1 / 2 : ℝ) • ((x : XSpace) + (y : XSpace))‖ ^ 2 ≤
    1 - (1 / 12 : ℝ) * ‖(x : XSpace) - (y : XSpace)‖ ^ 2
  exact norm_midpoint_sq_le hx hy

/-- The midpoint estimate equips the one-sorted reduct with Mathlib's
uniform-convexity structure. -/
@[reducible] noncomputable def limitBanachSpaceUniformConvexSpace
    (initial : BallWitnessIndexing expansionStructure) :
    UniformConvexSpace (LimitBanachSpace initial) :=
  NormFormula.uniformConvexSpaceOfMidpointEstimate
    (limitBanachSpace_norm_midpoint_sq_le initial)

/-- The one-sorted reduct contains no isomorphic copy of `c₀`, by its
quantitative equivalence with the auxiliary Hilbert subspace. -/
theorem limitBanachSpace_not_containsIsomorphicCopyOfC0
    (initial : BallWitnessIndexing expansionStructure) :
    ¬ NormFormula.ContainsIsomorphicCopyOfC0 (LimitBanachSpace initial) := by
  exact NormFormula.not_containsIsomorphicCopyOfC0_of_equiv_innerProduct
    (limitContinuousLinearEquivHilbert initial) (Real.sqrt 3)
    (Real.sqrt_pos.2 (by norm_num))
    (limit_norm_symm_le_sqrtThree_mul_hilbert_norm initial)

end

end NormFormula.X.BallLanguage
