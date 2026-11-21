import NormFormula.Analytic.HilbertNoC0
import NormFormula.Analytic.MidpointUniformConvex
import NormFormula.ModelTheory.XSeparableIPModel

/-!
# Legacy conditional separable Hilbertian IP presentation

The final construction in the paper uses the complete theory of `XSpace`
expanded by its auxiliary Hilbert norm. Continuous compactness and downward
Löwenheim--Skolem produce a separable expanded model; forgetting the auxiliary
predicate gives the desired Banach space `W`.

This file retains the original post-transfer interface for historical and
comparison purposes.  It stores the Hilbert equivalence and midpoint estimate
as fields and is therefore not the assumption-free endpoint of the
formalization.  The public replacement is
`BallLanguage.SeparableHilbertianNormAddIPModel`, constructed by the typed
continuous-logic development; `XHilbertBallFinalModel.lean` derives its
Hilbert comparison, global midpoint estimate, uniform convexity, and no-`c₀`
conclusion without presentation hypotheses.
-/

namespace NormFormula.X

noncomputable section

universe v w z

variable (W : Type v) (H : Type w)
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The geometric and logical data transferred from the expanded complete
theory `T'` to the separable model. The type `H` is the complete auxiliary
Hilbert norm on the same vector space, presented through a linear
equivalence. -/
structure HilbertianSeparableIPModelPresentation
    (S : NormFormula.SeparableIPModelSemantics XSpace W) where
  toSeparableIPModelPresentation : SeparableIPModelPresentation W S
  linearEquivHilbert : W ≃ₗ[ℝ] H
  hilbert_norm_le_norm : ∀ x : W, ‖linearEquivHilbert x‖ ≤ ‖x‖
  norm_symm_le_sqrtThree_mul_hilbert_norm : ∀ h : H,
    ‖linearEquivHilbert.symm h‖ ≤ Real.sqrt 3 * ‖h‖
  norm_midpoint_sq_le : ∀ x y : W, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
    ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤
      1 - (1 / 12 : ℝ) * ‖x - y‖ ^ 2

namespace HilbertianSeparableIPModelPresentation

variable {W : Type v} {H : Type w}
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {S : NormFormula.SeparableIPModelSemantics XSpace W}

/-- The transferred comparison inequalities turn the algebraic identity with
the auxiliary Hilbert norm into an actual continuous linear equivalence. -/
def continuousLinearEquivHilbert
    (P : HilbertianSeparableIPModelPresentation W H S) : W ≃L[ℝ] H :=
  P.linearEquivHilbert.toContinuousLinearEquivOfBounds 1 (Real.sqrt 3)
    (fun x ↦ by simpa using P.hilbert_norm_le_norm x)
    (fun h ↦ by
      simpa using P.norm_symm_le_sqrtThree_mul_hilbert_norm h)

/-- The transferred midpoint sentence supplies a genuine uniform-convexity
structure on the extracted model. -/
@[reducible] def uniformConvexSpace
    (P : HilbertianSeparableIPModelPresentation W H S) :
    UniformConvexSpace W :=
  NormFormula.uniformConvexSpaceOfMidpointEstimate P.norm_midpoint_sq_le

/-- The precise quantitative meaning of the paper's phrase
"`√3`-isomorphic to Hilbert space". -/
def IsSqrtThreeIsomorphicToHilbert
    (P : HilbertianSeparableIPModelPresentation W H S) : Prop :=
  (Nonempty (InnerProductSpace ℝ H) ∧ Nonempty (CompleteSpace H)) ∧
    (∀ x : W, ‖P.continuousLinearEquivHilbert x‖ ≤ ‖x‖) ∧
      ∀ h : H,
        ‖P.continuousLinearEquivHilbert.symm h‖ ≤ Real.sqrt 3 * ‖h‖

/-- The transferred linear equivalence has the quantitative constants asserted
in the paper. -/
theorem isSqrtThreeIsomorphicToHilbert
    (P : HilbertianSeparableIPModelPresentation W H S) :
    P.IsSqrtThreeIsomorphicToHilbert := by
  refine ⟨⟨⟨(inferInstance : InnerProductSpace ℝ H)⟩,
    ⟨(inferInstance : CompleteSpace H)⟩⟩, ⟨?_, ?_⟩⟩
  · intro x
    simpa [continuousLinearEquivHilbert] using P.hilbert_norm_le_norm x
  · intro h
    simpa [continuousLinearEquivHilbert] using
      P.norm_symm_le_sqrtThree_mul_hilbert_norm h

omit [CompleteSpace H] in
/-- The quantitative Hilbert equivalence and the finite signed-sum argument
show that the extracted model contains no isomorphic copy of `c₀`. -/
theorem not_containsIsomorphicCopyOfC0
    (P : HilbertianSeparableIPModelPresentation W H S) :
    ¬ NormFormula.ContainsIsomorphicCopyOfC0 W := by
  exact NormFormula.not_containsIsomorphicCopyOfC0_of_equiv_innerProduct
    P.continuousLinearEquivHilbert (Real.sqrt 3)
    (Real.sqrt_pos.2 (by norm_num))
    (fun h ↦ by
      simpa [continuousLinearEquivHilbert] using
        P.norm_symm_le_sqrtThree_mul_hilbert_norm h)

/-- Final assembly of Theorem `hilbertian-ip-space`: the extracted Banach
reduct is a separable model of `Th(X)`, its norm formula has an infinite IP
witness, it retains the fixed midpoint modulus and the quantitative Hilbert
equivalence, and it contains no isomorphic copy of `c₀`.

The `c₀` conclusion is proved directly from the Hilbert equivalence, without
using the not-yet-formalized Milman--Pettis theorem. -/
theorem extractedModel_has_all_conclusions
    (P : HilbertianSeparableIPModelPresentation W H S) :
    S.IsModelOfHomeTheory ∧
      TopologicalSpace.IsSeparable (Set.univ : Set W) ∧
      NormFormula.HasBoundedInfiniteIPWitness
        (fun x y : W ↦ ‖x + y‖)
        (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 6) ∧
      (∀ x y : W, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤
          1 - (1 / 12 : ℝ) * ‖x - y‖ ^ 2) ∧
      UniformConvexSpace W ∧
      P.IsSqrtThreeIsomorphicToHilbert ∧
      ¬ NormFormula.ContainsIsomorphicCopyOfC0 W := by
  have hlogical :=
    P.toSeparableIPModelPresentation.extractedModel_isSeparable_and_norm_hasIP
  exact ⟨hlogical.1, hlogical.2.1, hlogical.2.2,
    P.norm_midpoint_sq_le, P.uniformConvexSpace,
    P.isSqrtThreeIsomorphicToHilbert,
    P.not_containsIsomorphicCopyOfC0⟩

end HilbertianSeparableIPModelPresentation

end


end NormFormula.X
