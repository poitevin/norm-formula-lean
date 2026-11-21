import NormFormula.ContinuousLogic.XHilbertBallFinalModel
import NormFormula.ContinuousLogic.XHilbertBallStandardReduct
import NormFormula.Analytic.XPositiveIndex
import NormFormula.ContinuousLogic.FullBanachBallTheoryIP
import NormFormula.ContinuousLogic.YFullBanachBallTheoryNIP
import NormFormula.ContinuousLogic.NormAddFixedBalls
import NormFormula.ContinuousLogic.XTheoryIP
import NormFormula.ContinuousLogic.YFinitePatternNIP
import NormFormula.ModelTheory.YTheorem
import NormFormula.ModelTheory.XYTheorem

/-!
# Public paper-claim interface

This module collects assumption-free statements for the concrete examples
and a separable elementary extension of `X` with IP. For `X` and `X ⊕₂ Y`,
theory-level IP is stated in the full predicate-free standard Banach ball language.
The `Y` complete-theory NIP theorem is stated in that same full language at
every independently chosen pair of rational row and parameter radii, and the
separable model `W` is constructed in the full typed X expansion.

The construction uses `XSpace`, which includes the pure Hilbert block at
index zero. The Section 6 theorem uses the linear isometry with the paper's
positive-index sum to state the conclusion for that sum.
-/

namespace NormFormula.PaperClaims

noncomputable section

open NormFormula.ContinuousLogic

/-- Earlier normalized-language version of the conclusion about `X`:
stability is for the concrete norm formula on `X`, and theory IP is in the
minimal normalized bounded norm-addition language. -/
theorem x_stable_and_normalizedNormTheoryIP :
    NormFormula.IsStableOnBounded NormFormula.X.normTranslate ∧
      NormFormulaHasIPInCompleteTheory NormFormula.X.XSpace :=
  NormFormula.X.normFormula_stableInX_and_hasSemanticTheoryIP

/-- Full-language conclusion for the formal `XSpace`: the
concrete norm formula is stable on `X`, but its radius-`2` instance has IP in
the complete predicate-free standard Banach ball theory of `X`. -/
def XFullLanguageConclusion : Prop :=
    NormFormula.IsStableOnBounded NormFormula.X.normTranslate ∧
      (predicateFreeNormAddFormula 2 2).HasIPInCompleteTheory
        (standardBanachBallStructure NormFormula.X.XSpace)

theorem x_stable_and_fullBanachBallTheoryIP :
    XFullLanguageConclusion :=
  ⟨NormFormula.X.normFormula_stableInX_and_hasSemanticTheoryIP.1,
    NormFormula.X.predicateFreeNormAddFormula_hasIPInCompleteTheory⟩

/-- Assumption-free complete-theory NIP for `Y` on every positive ball,
together with instability of the concrete norm formula. -/
theorem y_unstable_and_ballTheoryNIP :
    (¬ NormFormula.IsStableOnBounded
      NormFormula.HalfGraph.Y.normPredicateTranslate) ∧
      ∀ (R : ℝ) (hR : 0 < R),
        MultiFormula.IsNIPInCompleteTheory
          (NormFormula.HalfGraph.Y.ContinuousLanguage.reductStructure R hR)
          NormFormula.HalfGraph.Y.ContinuousLanguage.normFormula := by
  exact ⟨NormFormula.HalfGraph.Y.normPredicateTranslate_not_isStableOnBounded,
    NormFormula.HalfGraph.Y.ContinuousLanguage.normFormula_isNIPInCompleteTheory⟩

/-- Exact full-language counterpart of the paper's theorem about `Y`: the
concrete norm formula is unstable, while every independently bounded typed
instance is NIP in the complete predicate-free standard Banach ball theory
of `Y`. -/
def YFullLanguageConclusion : Prop :=
    (¬ NormFormula.IsStableOnBounded
      NormFormula.HalfGraph.Y.normPredicateTranslate) ∧
      ∀ rowRadius parameterRadius : ℚ≥0,
        (predicateFreeNormAddFormula rowRadius parameterRadius).IsNIPInCompleteTheory
          (standardBanachBallStructure NormFormula.HalfGraph.Y)

theorem y_unstable_and_fullBanachBallTheoryNIP :
    YFullLanguageConclusion :=
  ⟨NormFormula.HalfGraph.Y.normPredicateTranslate_not_isStableOnBounded,
    NormFormula.HalfGraph.Y.predicateFreeNormAddFormula_isNIPInCompleteTheory_mixed⟩

/-- Earlier normalized-language version of the direct-sum corollary: instability
and NIP hold on every distinguished positive ball, while theory IP is in the
minimal normalized bounded norm-addition language. -/
theorem xy_unstable_ballNIP_and_normalizedNormTheoryIP :
    (¬ NormFormula.IsStableOnBounded NormFormula.XY.normTranslate) ∧
      NormFormulaIsNIPOnPositiveBalls NormFormula.XY.XYSpace ∧
      NormFormulaHasIPInCompleteTheory NormFormula.XY.XYSpace :=
  NormFormula.XY.normFormula_unstable_locallyNIP_and_theoryIP

/-- Full-language conclusion for the formal direct sum: the norm formula is
unstable and NIP on every distinguished positive ball, while its radius-`2`
instance has IP in the complete predicate-free standard Banach ball theory of
`X ⊕₂ Y`. -/
theorem xy_unstable_ballNIP_and_fullBanachBallTheoryIP :
    (¬ NormFormula.IsStableOnBounded NormFormula.XY.normTranslate) ∧
      NormFormulaIsNIPOnPositiveBalls NormFormula.XY.XYSpace ∧
      (predicateFreeNormAddFormula 2 2).HasIPInCompleteTheory
        (standardBanachBallStructure NormFormula.XY.XYSpace) :=
  ⟨NormFormula.XY.normFormula_unstable_locallyNIP_and_theoryIP.1,
    NormFormula.XY.normFormula_unstable_locallyNIP_and_theoryIP.2.1,
    NormFormula.XY.predicateFreeNormAddFormula_hasIPInCompleteTheory⟩

/-- The distinguished-space NIP conclusions are valid for every independent
pair of nonnegative row and parameter ball radii, including either radius
being zero. -/
theorem concrete_normFormula_NIP_on_arbitrary_fixed_balls :
    (∀ (Rₓ Rᵧ : ℝ) (hRₓ : 0 ≤ Rₓ) (hRᵧ : 0 ≤ Rᵧ),
      MultiFormula.IsNIPOnStructure
        (normAddFixedMultiStructure (E := NormFormula.X.XSpace)
          Rₓ Rᵧ hRₓ hRᵧ) normAddMultiFormula) ∧
    (∀ (Rₓ Rᵧ : ℝ) (hRₓ : 0 ≤ Rₓ) (hRᵧ : 0 ≤ Rᵧ),
      MultiFormula.IsNIPOnStructure
        (normAddFixedMultiStructure (E := NormFormula.HalfGraph.Y)
          Rₓ Rᵧ hRₓ hRᵧ) normAddMultiFormula) ∧
    (∀ (Rₓ Rᵧ : ℝ) (hRₓ : 0 ≤ Rₓ) (hRᵧ : 0 ≤ Rᵧ),
      MultiFormula.IsNIPOnStructure
        (normAddFixedMultiStructure (E := NormFormula.XY.XYSpace)
          Rₓ Rᵧ hRₓ hRᵧ) normAddMultiFormula) :=
  ⟨NormFormula.X.normAddFixedMultiFormula_isNIPOnStructure,
    NormFormula.HalfGraph.Y.normAddFixedMultiFormula_isNIPOnStructure,
    NormFormula.XY.normAddFixedMultiFormula_isNIPOnStructure⟩

/-- The geometric part of the main theorem, strengthened by including the
same conclusions for the direct sum. -/
def ConcreteGeometricConclusions : Prop :=
    (TopologicalSpace.IsSeparable
      (Set.univ : Set NormFormula.X.XSpace) ∧
      (∀ x y : NormFormula.X.XSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤
          1 - (1 / 12 : ℝ) * ‖x - y‖ ^ 2) ∧
      UniformConvexSpace NormFormula.X.XSpace ∧
      (∀ x : NormFormula.X.XSpace,
        ‖NormFormula.X.toHilbert x‖ ≤ ‖x‖) ∧
      (∀ z : NormFormula.X.XHilbertSpace,
        ‖NormFormula.X.ofHilbert z‖ ≤ Real.sqrt 3 * ‖z‖)) ∧
    (TopologicalSpace.IsSeparable
      (Set.univ : Set NormFormula.HalfGraph.Y) ∧
      (∀ x y : NormFormula.HalfGraph.Y, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤
          1 - (1 / 12 : ℝ) * ‖x - y‖ ^ 2) ∧
      UniformConvexSpace NormFormula.HalfGraph.Y ∧
      (∀ y : NormFormula.HalfGraph.Y,
        ‖y.toHilbert‖ ≤ ‖y‖) ∧
      (∀ z : NormFormula.HalfGraph.HilbertSpace,
        ‖NormFormula.HalfGraph.Y.linearEquivHilbert.symm z‖ ≤
          Real.sqrt 3 * ‖z‖)) ∧
    (TopologicalSpace.IsSeparable
      (Set.univ : Set NormFormula.XY.XYSpace) ∧
      (∀ x y : NormFormula.XY.XYSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤
          1 - (1 / 12 : ℝ) * ‖x - y‖ ^ 2) ∧
      UniformConvexSpace NormFormula.XY.XYSpace ∧
      (∀ z : NormFormula.XY.XYSpace,
        ‖NormFormula.XY.toHilbert z‖ ≤ ‖z‖) ∧
      (∀ z : NormFormula.XY.XYHilbertSpace,
        ‖NormFormula.XY.ofHilbert z‖ ≤ Real.sqrt 3 * ‖z‖))

/-- The three concrete spaces have the separability, exact `1/12` midpoint
estimate, derived uniform convexity, and quantitative `√3` Hilbert
comparisons asserted in the paper. -/
theorem concrete_geometric_conclusions :
    ConcreteGeometricConclusions := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨NormFormula.X.verified_geometric_conclusions.1,
      NormFormula.X.verified_geometric_conclusions.2.1, inferInstance,
      NormFormula.X.verified_geometric_conclusions.2.2.1,
      NormFormula.X.verified_geometric_conclusions.2.2.2⟩
  · exact ⟨NormFormula.HalfGraph.Y.verified_geometric_conclusions.1,
      NormFormula.HalfGraph.Y.verified_geometric_conclusions.2.1,
      inferInstance,
      NormFormula.HalfGraph.Y.verified_geometric_conclusions.2.2.1,
      NormFormula.HalfGraph.Y.verified_geometric_conclusions.2.2.2⟩
  · exact ⟨NormFormula.XY.verified_geometric_conclusions.1,
      NormFormula.XY.verified_geometric_conclusions.2.1, inferInstance,
      NormFormula.XY.verified_geometric_conclusions.2.2.1,
      NormFormula.XY.verified_geometric_conclusions.2.2.2⟩

/-- A separable elementary extension of `E`. The real linear isometry from
`E` preserves all formulas on all rational ball sorts.
The standard radius-`2` norm-addition formula has an infinite IP witness.
The same carrier is uniformly convex with the exact midpoint constant, `√3`-isomorphic to its
reconstructed Hilbert carrier, and contains no isomorphic copy of `c₀`. -/
def SeparableHilbertianIPModelConclusion (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] : Prop :=
    ∃ M : NormFormula.X.BallLanguage.SeparableHilbertianNormAddIPModel,
      BallSameCompleteTheory
        (standardBanachBallStructure E)
        (standardBanachBallStructure M.model.CompletedDirectedPoint) ∧
      (∃ e : E →ₗᵢ[ℝ] M.model.CompletedDirectedPoint,
        IsElementaryBanachEmbedding e) ∧
      (predicateFreeNormAddFormula 2 2).HasInfiniteIPWitness
        (standardBanachBallStructure M.model.CompletedDirectedPoint)
        (Real.sqrt 3 / 8) (Real.sqrt 6 / 8) ∧
      TopologicalSpace.SeparableSpace M.model.CompletedDirectedPoint ∧
      TopologicalSpace.SeparableSpace M.model.AuxiliaryHilbertCarrier ∧
      M.model.HasCompletedNormAddWitness
        2 (Real.sqrt 3) (Real.sqrt 6) ∧
      (∀ x y : M.model.CompletedDirectedPoint,
        ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤
            1 - (1 / 12 : ℝ) * ‖x - y‖ ^ 2) ∧
      UniformConvexSpace M.model.CompletedDirectedPoint ∧
      M.IsSqrtThreeIsomorphicToHilbert ∧
      ¬ NormFormula.ContainsIsomorphicCopyOfC0
        M.model.CompletedDirectedPoint

private theorem exists_separable_hilbertian_ip_model_of_equiv
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : E ≃ₗᵢ[ℝ] NormFormula.X.XSpace) :
    SeparableHilbertianIPModelConclusion E := by
  obtain ⟨M⟩ :=
    NormFormula.X.BallLanguage.exists_separableHilbertian_normAddIPModel
  have hElementary :
      IsElementaryBanachEmbedding (M.elementaryCopy.embedding.comp e.toLinearIsometry) := by
    apply IsElementaryBanachEmbedding.comp
    · exact M.elementaryCopy.embedding_isElementary
    · exact IsElementaryBanachEmbedding.of_linearIsometryEquiv e
  exact ⟨M,
    IsElementaryBanachEmbedding.sameCompleteTheory hElementary,
    ⟨M.elementaryCopy.embedding.comp e.toLinearIsometry, hElementary⟩,
    M.model.predicateFreeNormAddFormula_hasInfiniteIPWitness_of_completed_two
      M.normAddWitness_two,
    M.completedSeparable, M.auxiliaryHilbertSeparable, M.normAddWitness_two,
    M.norm_midpoint_sq_le, M.uniformConvexSpace, M.isSqrtThreeIsomorphicToHilbert,
    M.not_containsIsomorphicCopyOfC0⟩

/-- Section 6 for the paper's space with block dimensions `1, 2, …`. -/
theorem exists_separable_hilbertian_ip_model :
    SeparableHilbertianIPModelConclusion NormFormula.X.XPositiveSpace :=
  exists_separable_hilbertian_ip_model_of_equiv NormFormula.X.xSpaceEquivPositive.symm

/-- Public assembly of the formalized conclusions: the full-language model-theoretic
conclusions for `X` and `Y`, the concrete geometry (with the direct-sum
strengthening), and the constructed separable elementary extension `W`.
The same `XSpace` is used in all conjuncts involving `X`. -/
theorem main_theorem_zeroBased :
    XFullLanguageConclusion ∧
      YFullLanguageConclusion ∧
      ConcreteGeometricConclusions ∧
      SeparableHilbertianIPModelConclusion NormFormula.X.XSpace :=
  ⟨x_stable_and_fullBanachBallTheoryIP,
    y_unstable_and_fullBanachBallTheoryNIP,
    concrete_geometric_conclusions,
    exists_separable_hilbertian_ip_model_of_equiv (LinearIsometryEquiv.refl ℝ _)⟩

end

end NormFormula.PaperClaims
