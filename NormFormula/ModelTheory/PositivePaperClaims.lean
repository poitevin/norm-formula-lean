import NormFormula.ModelTheory.PaperClaims
import NormFormula.Analytic.MidpointUniformConvex

/-! # Public conclusions for the paper's positive-index presentation -/

namespace NormFormula
noncomputable section
open ContinuousLogic TopologicalSpace

namespace XY
abbrev XYPositiveSpace := WithLp 2 (X.XPositiveSpace × HalfGraph.Y)
def positiveEquiv : XYPositiveSpace ≃ₗᵢ[ℝ] XYSpace :=
  X.xSpaceEquivPositive.symm.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ _)
end XY

namespace PaperClaims

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_stable_of_equiv (e : E ≃ₗᵢ[ℝ] F)
    (h : IsStableOnBounded (fun x y : F ↦ ‖x + y‖)) :
    IsStableOnBounded (fun x y : E ↦ ‖x + y‖) := by
  simpa only [← e.map_add, e.norm_map] using
    h.comap e e (fun x ↦ (e.norm_map x).le) (fun x ↦ (e.norm_map x).le)

theorem norm_theoryIP_of_equiv (e : E ≃ₗᵢ[ℝ] F) (r s : ℚ≥0)
    (h : (predicateFreeNormAddFormula r s).HasIPInCompleteTheory
      (standardBanachBallStructure F)) :
    (predicateFreeNormAddFormula r s).HasIPInCompleteTheory
      (standardBanachBallStructure E) := by
  obtain ⟨M, hM, witness⟩ := h
  refine ⟨M, ?_, witness⟩
  intro sentence
  exact (IsElementaryBanachEmbedding.sameCompleteTheory
    (IsElementaryBanachEmbedding.of_linearIsometryEquiv e) sentence).trans (hM sentence)

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_ballNIP_of_equiv (e : E ≃ₗᵢ[ℝ] F)
    (h : NormFormulaIsNIPOnPositiveBalls F) : NormFormulaIsNIPOnPositiveBalls E := by
  intro R hR
  rintro ⟨low, high, hgap, rows, hrows⟩
  apply h R hR
  let mapBall (x : PositiveNormBall E R) : PositiveNormBall F R :=
    ⟨e x.1, by simpa only [e.norm_map] using x.2⟩
  refine ⟨low, high, hgap, fun i ↦ mapBall (rows i), ?_⟩
  intro A B hAB
  obtain ⟨y, hyA, hyB⟩ := hrows A B hAB
  refine ⟨mapBall y, ?_, ?_⟩
  · intro i hi
    simpa only [MultiFormula.binaryValue, normAddMultiFormula,
      MultiFormula.realize, normAddMultiStructure, mapBall, normAddTruth,
      ← e.map_add, e.norm_map] using hyA i hi
  · intro i hi
    simpa only [MultiFormula.binaryValue, normAddMultiFormula,
      MultiFormula.realize, normAddMultiStructure, mapBall, normAddTruth,
      ← e.map_add, e.norm_map] using hyB i hi

def MidpointEstimate (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
    ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤ 1 - (1 / 12 : ℝ) * ‖x - y‖ ^ 2

omit [CompleteSpace E] [CompleteSpace F] in
theorem midpoint_of_equiv (e : E ≃ₗᵢ[ℝ] F) (h : MidpointEstimate F) :
    MidpointEstimate E := by
  intro x y hx hy
  simpa only [← e.map_add, ← e.map_sub, ← e.map_smul, e.norm_map] using
    h (e x) (e y) (by simpa only [e.norm_map] using hx)
      (by simpa only [e.norm_map] using hy)

omit [CompleteSpace E] [CompleteSpace F] in
theorem separable_of_equiv (e : E ≃ₗᵢ[ℝ] F) [SeparableSpace F] : SeparableSpace E := by
  have h := isSeparable_range e.symm.continuous
  rw [e.symm.surjective.range_eq] at h
  exact isSeparable_univ_iff.mp h

def PositiveXFullLanguageConclusion : Prop :=
  IsStableOnBounded (fun x y : X.XPositiveSpace ↦ ‖x + y‖) ∧
    (predicateFreeNormAddFormula 2 2).HasIPInCompleteTheory
      (standardBanachBallStructure X.XPositiveSpace)

theorem x_positive_stable_and_fullBanachBallTheoryIP : PositiveXFullLanguageConclusion :=
  ⟨norm_stable_of_equiv X.xSpaceEquivPositive.symm X.normTranslate_isStableOnBounded,
    norm_theoryIP_of_equiv X.xSpaceEquivPositive.symm 2 2
      X.predicateFreeNormAddFormula_hasIPInCompleteTheory⟩

theorem xy_positive_unstable_ballNIP_and_fullBanachBallTheoryIP :
    (¬ IsStableOnBounded (fun x y : XY.XYPositiveSpace ↦ ‖x + y‖)) ∧
      NormFormulaIsNIPOnPositiveBalls XY.XYPositiveSpace ∧
      (predicateFreeNormAddFormula 2 2).HasIPInCompleteTheory
        (standardBanachBallStructure XY.XYPositiveSpace) := by
  refine ⟨?_, norm_ballNIP_of_equiv XY.positiveEquiv
    xy_unstable_ballNIP_and_fullBanachBallTheoryIP.2.1,
    norm_theoryIP_of_equiv XY.positiveEquiv 2 2
      xy_unstable_ballNIP_and_fullBanachBallTheoryIP.2.2⟩
  intro h
  exact xy_unstable_ballNIP_and_fullBanachBallTheoryIP.1
    (norm_stable_of_equiv XY.positiveEquiv.symm h)

def positiveXHilbertEquiv : X.XPositiveSpace ≃L[ℝ] X.XHilbertSpace :=
  X.xSpaceEquivPositive.symm.toContinuousLinearEquiv.trans X.continuousLinearEquivHilbertSum

def positiveXYHilbertEquiv : XY.XYPositiveSpace ≃L[ℝ] XY.XYHilbertSpace :=
  XY.positiveEquiv.toContinuousLinearEquiv.trans XY.continuousLinearEquivHilbertSum

def GeometryWithHilbertEquiv {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (e : E ≃L[ℝ] H) : Prop :=
  SeparableSpace E ∧ MidpointEstimate E ∧ UniformConvexSpace E ∧
    (∀ x, ‖e x‖ ≤ ‖x‖) ∧ ∀ z, ‖e.symm z‖ ≤ Real.sqrt 3 * ‖z‖

theorem positive_geometric_conclusions :
    GeometryWithHilbertEquiv positiveXHilbertEquiv ∧
    GeometryWithHilbertEquiv positiveXYHilbertEquiv := by
  have hx : MidpointEstimate X.XPositiveSpace :=
    midpoint_of_equiv X.xSpaceEquivPositive.symm (fun _ _ ↦ X.norm_midpoint_sq_le)
  have hxy : MidpointEstimate XY.XYPositiveSpace :=
    midpoint_of_equiv XY.positiveEquiv (fun _ _ ↦ XY.norm_midpoint_sq_le)
  constructor
  · refine ⟨separable_of_equiv X.xSpaceEquivPositive.symm, hx,
      uniformConvexSpaceOfMidpointEstimate hx, ?_, ?_⟩
    · intro x
      simpa [positiveXHilbertEquiv] using X.norm_toHilbert_le (X.xSpaceEquivPositive.symm x)
    · intro z
      simpa [positiveXHilbertEquiv] using X.norm_ofHilbert_le z
  · refine ⟨separable_of_equiv XY.positiveEquiv, hxy,
      uniformConvexSpaceOfMidpointEstimate hxy, ?_, ?_⟩
    · intro x
      simpa [positiveXYHilbertEquiv] using XY.norm_toHilbert_le (XY.positiveEquiv x)
    · intro z
      simpa [positiveXYHilbertEquiv] using XY.norm_ofHilbert_le z

/-- The main theorem uses the paper's positive-index space in every clause. -/
theorem main_theorem :
    PositiveXFullLanguageConclusion ∧ YFullLanguageConclusion ∧
      GeometryWithHilbertEquiv positiveXHilbertEquiv ∧
      GeometryWithHilbertEquiv HalfGraph.Y.continuousLinearEquivHilbert ∧
      SeparableHilbertianIPModelConclusion X.XPositiveSpace := by
  refine ⟨x_positive_stable_and_fullBanachBallTheoryIP,
    y_unstable_and_fullBanachBallTheoryNIP, positive_geometric_conclusions.1,
    ?_, exists_separable_hilbertian_ip_model⟩
  exact ⟨inferInstance, fun _ _ ↦ HalfGraph.Y.norm_midpoint_sq_le, inferInstance,
    HalfGraph.Y.hilbert_norm_le_norm,
    fun z ↦ HalfGraph.Y.norm_le_sqrtThree_mul_hilbert_norm
      (HalfGraph.Y.linearEquivHilbert.symm z)⟩

end PaperClaims
end
end NormFormula
