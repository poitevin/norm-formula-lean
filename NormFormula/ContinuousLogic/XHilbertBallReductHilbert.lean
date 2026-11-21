import NormFormula.ContinuousLogic.XHilbertBallReductCarrier

/-!
# The auxiliary Hilbert space of the one-sorted reduct

The global continuous linear equivalence from `XSpace` to its Hilbert model
restricts to the closed reduct subspace.  Its image is closed, hence complete,
and inherits an inner-product structure.  This supplies the actual auxiliary
Hilbert type and the quantitative norm comparisons required by the paper's
final presentation.
-/

namespace NormFormula.X.BallLanguage

noncomputable section

open Set
open NormFormula.ContinuousLogic

/-- The image of the one-sorted reduct inside the global Hilbert model. -/
def limitHilbertSubspace
    (initial : BallWitnessIndexing expansionStructure) :
    Submodule ℝ XHilbertSpace :=
  (limitBanachSubspace initial).map
    continuousLinearEquivHilbertSum.toLinearMap

/-- The auxiliary Hilbert space carried by the one-sorted reduct. -/
abbrev LimitHilbertSpace
    (initial : BallWitnessIndexing expansionStructure) :=
  limitHilbertSubspace initial

/-- The image subspace is closed because a continuous linear equivalence is
a homeomorphism and the reduct subspace is closed. -/
theorem limitHilbertSubspace_isClosed
    (initial : BallWitnessIndexing expansionStructure) :
    IsClosed (limitHilbertSubspace initial : Set XHilbertSpace) := by
  rw [limitHilbertSubspace, Submodule.map_coe]
  exact continuousLinearEquivHilbertSum.isClosed_image.mpr
    (Submodule.isClosed_topologicalClosure _)

/-- The auxiliary Hilbert image is complete. -/
@[reducible] noncomputable def limitHilbertSpaceCompleteSpace
    (initial : BallWitnessIndexing expansionStructure) :
    CompleteSpace (LimitHilbertSpace initial) :=
  (limitHilbertSubspace_isClosed initial).completeSpace_coe

/-- Restriction of the global Hilbert equivalence to the reduct and its image. -/
def limitContinuousLinearEquivHilbert
    (initial : BallWitnessIndexing expansionStructure) :
    LimitBanachSpace initial ≃L[ℝ] LimitHilbertSpace initial :=
  continuousLinearEquivHilbertSum.submoduleMap
    (limitBanachSubspace initial)

/-- The algebraic linear equivalence underlying the restricted continuous
Hilbert equivalence. -/
def limitLinearEquivHilbert
    (initial : BallWitnessIndexing expansionStructure) :
    LimitBanachSpace initial ≃ₗ[ℝ] LimitHilbertSpace initial :=
  (limitContinuousLinearEquivHilbert initial).toLinearEquiv

@[simp]
theorem limitContinuousLinearEquivHilbert_apply
    (initial : BallWitnessIndexing expansionStructure)
    (x : LimitBanachSpace initial) :
    ((limitContinuousLinearEquivHilbert initial x :
      LimitHilbertSpace initial) : XHilbertSpace) = toHilbert (x : XSpace) :=
  rfl

@[simp]
theorem limitContinuousLinearEquivHilbert_symm_apply
    (initial : BallWitnessIndexing expansionStructure)
    (h : LimitHilbertSpace initial) :
    (((limitContinuousLinearEquivHilbert initial).symm h :
      LimitBanachSpace initial) : XSpace) = ofHilbert (h : XHilbertSpace) :=
  rfl

/-- The restricted forward Hilbert map does not increase the norm. -/
theorem limit_hilbert_norm_le_norm
    (initial : BallWitnessIndexing expansionStructure)
    (x : LimitBanachSpace initial) :
    ‖limitLinearEquivHilbert initial x‖ ≤ ‖x‖ := by
  change ‖toHilbert (x : XSpace)‖ ≤ ‖(x : XSpace)‖
  exact norm_toHilbert_le (x : XSpace)

/-- The inverse restricted Hilbert map has norm at most `√3`. -/
theorem limit_norm_symm_le_sqrtThree_mul_hilbert_norm
    (initial : BallWitnessIndexing expansionStructure)
    (h : LimitHilbertSpace initial) :
    ‖(limitLinearEquivHilbert initial).symm h‖ ≤
      Real.sqrt 3 * ‖h‖ := by
  change ‖ofHilbert (h : XHilbertSpace)‖ ≤
    Real.sqrt 3 * ‖(h : XHilbertSpace)‖
  exact norm_ofHilbert_le (h : XHilbertSpace)

end

end NormFormula.X.BallLanguage
