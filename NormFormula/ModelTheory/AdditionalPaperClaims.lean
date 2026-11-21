import NormFormula.ModelTheory.PositivePaperClaims
import NormFormula.ModelTheory.UltrapowerIP
import NormFormula.ContinuousLogic.MultiCompactnessAlong
import NormFormula.ContinuousLogic.HilbertTheoryNIP
import NormFormula.Examples.Bollobas
import NormFormula.Examples.DirectMembership
import NormFormula.Examples.XInfinity

/-! # The remaining general lemmas and examples in the paper -/
namespace NormFormula
noncomputable section
open ContinuousLogic Filter

/-- The local direct-sum lemma on independently fixed nonnegative balls. -/
theorem normAddFixedMultiFormula_isNIPOnStructure_l2Sum
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hE : NormFormulaIsNIPOnPositiveBalls E) (hF : NormFormulaIsNIPOnPositiveBalls F)
    (R S : ℝ) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    MultiFormula.IsNIPOnStructure
      (normAddFixedMultiStructure (E := WithLp 2 (E×F)) R S hR hS) normAddMultiFormula :=
  normAddFixedMultiFormula_isNIPOnStructure_of_common R S hR hS
    (normFormulaIsNIPOnPositiveBalls_l2Sum hE hF _ (fixedBallCommonRadius_pos hR hS))

namespace XY

theorem positive_norm_ultrapower_hasInfiniteIPWitness
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    HasBoundedInfiniteIPWitness
      (fun x y : BanachUltrapower U XYPositiveSpace ↦ ‖x+y‖)
      (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 6) :=
  norm_hasInfiniteIPWitness_ultrapower_of_finitePatterns U hU
    (HasIPPatternsInEveryDimension.of_norm_equiv positiveEquiv
      normTranslate_hasIPPatternsInEveryDimension)
end XY

namespace PaperClaims

/-- The public direct-sum assertion includes every free ultrafilter. -/
theorem xy_positive_with_every_ultrapower :
    (¬ IsStableOnBounded (fun x y : XY.XYPositiveSpace ↦ ‖x+y‖)) ∧
      NormFormulaIsNIPOnPositiveBalls XY.XYPositiveSpace ∧
      (∀ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ atTop →
        HasBoundedInfiniteIPWitness
          (fun x y : BanachUltrapower U XY.XYPositiveSpace ↦ ‖x+y‖)
          (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 6)) :=
  ⟨xy_positive_unstable_ballNIP_and_fullBanachBallTheoryIP.1,
    xy_positive_unstable_ballNIP_and_fullBanachBallTheoryIP.2.1,
    XY.positive_norm_ultrapower_hasInfiniteIPWitness⟩

/-- Bollobás's precise additive norm, for every positive coefficient. -/
theorem additive_norm_conclusion (ε : ℝ) (hε : 0 < ε) :
    (¬ IsStableOnBounded (fun x y : Bollobas.Space ε hε ↦ ‖x+y‖)) ∧
      ∀ r s : ℚ≥0, (predicateFreeNormAddFormula r s).IsNIPInCompleteTheory
        (standardBanachBallStructure (Bollobas.Space ε hε)) :=
  ⟨Bollobas.norm_unstable ε hε, Bollobas.fullTheoryNIP ε hε⟩

/-- The direct membership example is a separable uniformly convex Hilbertian
space with IP in the same carrier and no isomorphic copy of `c₀`. -/
theorem direct_membership_conclusion :
    TopologicalSpace.SeparableSpace DirectMembership.Space ∧
      UniformConvexSpace DirectMembership.Space ∧
      HasBoundedInfiniteIPWitness (fun x y : DirectMembership.Space ↦ ‖x+y‖)
        (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 6) ∧
      (∀ x y : DirectMembership.Space, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        ‖(1/2:ℝ) • (x+y)‖^2 ≤ 1-(1/12:ℝ)*‖x-y‖^2) ∧
      (∀ x : DirectMembership.Space, ‖DirectMembership.hilbertEquiv x‖ ≤ ‖x‖) ∧
      (∀ h : HalfGraph.HilbertSpace, ‖DirectMembership.hilbertEquiv.symm h‖ ≤ Real.sqrt 3*‖h‖) ∧
      ¬ ContainsIsomorphicCopyOfC0 DirectMembership.Space :=
  ⟨inferInstance, inferInstance, DirectMembership.infiniteIP,
    fun _ _ ↦ DirectMembership.midpoint,
    fun x ↦ norm_le_augmentedNorm _ x.val,
    augmentedNorm_le_sqrtThree_mul _ DirectMembership.p_sq_bound,
    DirectMembership.no_c0⟩
end PaperClaims
end
end NormFormula
