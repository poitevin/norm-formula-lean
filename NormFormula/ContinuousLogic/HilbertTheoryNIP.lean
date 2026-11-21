import NormFormula.ContinuousLogic.HilbertStableNIP
import NormFormula.ContinuousLogic.BanachBallMixedNormAddReduct
import NormFormula.ModelTheory.UltrapowerIP
import NormFormula.Analytic.Separability
import NormFormula.ContinuousLogic.HilbertPredicateTransfer

/-! # The Hilbert row of the paper's table -/
namespace NormFormula.ContinuousLogic
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Uniform finite-pattern NIP follows from stability in the Hilbert
ultrapower, without a quantitative Hilbert entropy estimate. -/
theorem hilbertNorm_isBoundedLocalNIP_of_stability :
    IsBoundedLocalNIP (fun x y : H ↦ ‖x+y‖) := by
  apply isBoundedLocalNIP_of_no_patterns
  intro R S low high hgap hp
  exact Hilbert.not_hasBoundedInfiniteIPWitness hgap
    (norm_hasInfiniteIPWitness_ultrapower_of_finitePatterns
      indexUltrafilter indexUltrafilter_le_atTop hp)

theorem hilbert_norm_fullTheoryNIP [CompleteSpace H]
    (rowRadius parameterRadius : ℚ≥0) :
    (predicateFreeNormAddFormula rowRadius parameterRadius).IsNIPInCompleteTheory
      (standardBanachBallStructure H) := by
  apply BallFormula.isNIPInCompleteTheory_of_mixedNormAddMulti
  apply normAddMultiFormula_isNIPInCompleteTheory_ballNormAddMixedMultiStructure_of_boundedLocalNIP
  exact hilbertNorm_isBoundedLocalNIP_of_stability

/-- Norm stability and complete-theory NIP for the standard real `ℓ₂`. -/
theorem l2_stable_and_fullTheoryNIP :
    IsStableOnBounded (fun x y : HalfGraph.RealL2 ↦ ‖x+y‖) ∧
      ∀ r s : ℚ≥0, (predicateFreeNormAddFormula r s).IsNIPInCompleteTheory
        (standardBanachBallStructure HalfGraph.RealL2) :=
  ⟨hilbert_norm_isStableOnBounded, hilbert_norm_fullTheoryNIP⟩

/-- The norm formula is stable in every model of the full standard Banach
ball theory of a Hilbert space, on independent radii including zero. -/
theorem hilbert_norm_fullTheoryStable
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (rowRadius parameterRadius : ℚ≥0) :
    (predicateFreeNormAddFormula rowRadius parameterRadius).IsStableInCompleteTheory
      (standardBanachBallStructure K) := by
  let M := ballNormAddMixedMultiStructure (standardBanachBallStructure K)
    rowRadius parameterRadius
  have h : MultiFormula.IsStableInCompleteTheory M normAddMultiFormula := by
    apply hilbertPredicate_isStableInCompleteTheory M normAddMultiFormula
      (fun x ↦ x.1) (fun y ↦ y.1) rowRadius parameterRadius
      (rationalBallMetricBound (rowRadius + parameterRadius))
      (rationalBallMetricBound_pos _) (fun x ↦ x.2) (fun y ↦ y.2)
    intro x y
    exact predicateFreeNormAddFormula_value rowRadius parameterRadius _
  intro N hTheory
  exact h (ballNormAddMixedMultiStructure N rowRadius parameterRadius)
    (ballSameCompleteTheory_mixedNormAddMultiStructure _ _
      rowRadius parameterRadius hTheory)

/-- Section 3.1's stronger conclusion: stability of the norm formula in
`Th(ℓ₂)`, without asserting stability of every formula in the theory. -/
theorem l2_norm_stable_in_completeTheory (r s : ℚ≥0) :
    (predicateFreeNormAddFormula r s).IsStableInCompleteTheory
      (standardBanachBallStructure HalfGraph.RealL2) :=
  hilbert_norm_fullTheoryStable r s
end
end NormFormula.ContinuousLogic
