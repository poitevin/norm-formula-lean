import NormFormula.Analytic.SeparableHilbertClassification
import NormFormula.ModelTheory.PositivePaperClaims
import NormFormula.Examples.DirectMembership
import NormFormula.Examples.Bollobas

/-! # Quantitative isomorphisms to standard `ℓ₂` for the paper's spaces -/
namespace NormFormula
noncomputable section
open TopologicalSpace

/-- Identifying the separable Hilbert target with standard `ℓ₂` preserves
the operator-norm bounds of the equivalence in both directions. -/
theorem exists_equiv_l2_of_hilbert_equiv_le
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]
    (e : E ≃L[ℝ] H) (v : ℕ → E) (hv : LinearIndependent ℝ v) :
    ∃ J : E ≃L[ℝ] HalfGraph.RealL2,
      ‖J.toContinuousLinearMap‖ ≤ ‖e.toContinuousLinearMap‖ ∧
      ‖J.symm.toContinuousLinearMap‖ ≤ ‖e.symm.toContinuousLinearMap‖ := by
  obtain ⟨f⟩ := exists_hilbertEquivL2 (e ∘ v)
    (hv.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective))
  refine ⟨e.trans f.toContinuousLinearEquiv, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    change ‖f (e x)‖ ≤ ‖e.toContinuousLinearMap‖ * ‖x‖
    rw [f.norm_map]
    exact e.toContinuousLinearMap.le_opNorm x
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    change ‖e.symm (f.symm z)‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖z‖
    simpa only [LinearIsometryEquiv.norm_map] using
      e.symm.toContinuousLinearMap.le_opNorm (f.symm z)


/-- The distortion condition in the introduction of arXiv:2611.15930v2. -/
def IsSqrtThreeIsomorphicToL2 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∃ J : E ≃L[ℝ] HalfGraph.RealL2,
    ‖J.toContinuousLinearMap‖ * ‖J.symm.toContinuousLinearMap‖ ≤ Real.sqrt 3

private theorem isSqrtThreeIsomorphicToL2_of_hilbert_equiv
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]
    (e : E ≃L[ℝ] H) (v : ℕ → E) (hv : LinearIndependent ℝ v)
    (h₁ : ∀ x, ‖e x‖ ≤ ‖x‖) (h₂ : ∀ z, ‖e.symm z‖ ≤ Real.sqrt 3 * ‖z‖) :
    IsSqrtThreeIsomorphicToL2 E := by
  obtain ⟨J, hJ, hJinv⟩ := exists_equiv_l2_of_hilbert_equiv_le e v hv
  have he : ‖e.toContinuousLinearMap‖ ≤ 1 :=
    e.toContinuousLinearMap.opNorm_le_bound (by norm_num) (by simpa using h₁)
  have heinv : ‖e.symm.toContinuousLinearMap‖ ≤ Real.sqrt 3 :=
    e.symm.toContinuousLinearMap.opNorm_le_bound (Real.sqrt_nonneg _) h₂
  refine ⟨J, ?_⟩
  simpa only [one_mul] using
    mul_le_mul (hJ.trans he) (hJinv.trans heinv) (norm_nonneg _) (zero_le_one' ℝ)

namespace X

def independentRows (n : ℕ) : XSpace :=
  lp.single 2 n (⟨subsetVector ∅⟩ : BlockSpace n)

theorem independentRows_linearIndependent : LinearIndependent ℝ independentRows := by
  let f : XSpace →ₗ[ℝ] (ℕ → ℝ) :=
    { toFun := fun x n ↦ (x n).toHilbert (Sum.inr ∅)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  apply LinearIndependent.of_comp f
  convert Pi.linearIndependent_single_one ℕ ℝ using 1
  funext n m
  change (independentRows n m).toHilbert (Sum.inr ∅) = (Pi.single n (1:ℝ) : ℕ → ℝ) m
  by_cases h : m=n
  · subst m
    simp [independentRows, subsetVector]
  · rw [independentRows, lp.single_apply_ne _ _ _ h, Pi.single_eq_of_ne h]
    rfl

theorem positive_sqrtThree_isomorphic_l2 : IsSqrtThreeIsomorphicToL2 XPositiveSpace := by
  have h := PaperClaims.positive_geometric_conclusions.1
  exact isSqrtThreeIsomorphicToL2_of_hilbert_equiv PaperClaims.positiveXHilbertEquiv
    (xSpaceEquivPositive ∘ independentRows)
    (independentRows_linearIndependent.map' xSpaceEquivPositive.toLinearMap
      (LinearMap.ker_eq_bot.mpr xSpaceEquivPositive.injective)) h.2.2.2.1 h.2.2.2.2

theorem positive_isomorphic_l2 : Nonempty (XPositiveSpace ≃L[ℝ] HalfGraph.RealL2) := by
  obtain ⟨J, _⟩ := positive_sqrtThree_isomorphic_l2
  exact ⟨J⟩
end X

namespace HalfGraph

theorem xInY_linearIndependent : LinearIndependent ℝ xInY := by
  let f : Y →ₗ[ℝ] RealL2 :=
    { toFun := fun x ↦ x.toHilbert.fst, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  exact LinearIndependent.of_comp f l2_basis_linearIndependent

theorem y_sqrtThree_isomorphic_l2 : IsSqrtThreeIsomorphicToL2 Y :=
  isSqrtThreeIsomorphicToL2_of_hilbert_equiv Y.continuousLinearEquivHilbert
    xInY xInY_linearIndependent Y.hilbert_norm_le_norm
    (fun z ↦ Y.norm_le_sqrtThree_mul_hilbert_norm (Y.linearEquivHilbert.symm z))

theorem y_isomorphic_l2 : Nonempty (Y ≃L[ℝ] RealL2) := by
  obtain ⟨J, _⟩ := y_sqrtThree_isomorphic_l2
  exact ⟨J⟩
end HalfGraph

namespace XY

theorem xy_positive_sqrtThree_isomorphic_l2 : IsSqrtThreeIsomorphicToL2 XYPositiveSpace := by
  let f : X.XSpace →ₗ[ℝ] XYSpace :=
    { toFun := inX, map_add' := inX_add, map_smul' := fun r x ↦ by
        simp only [inX, ← WithLp.toLp_smul, Prod.smul_mk, smul_zero, RingHom.id_apply] }
  have hf : Function.Injective f := by intro x y h; exact congrArg WithLp.fst h
  let g := positiveEquiv.symm.toLinearMap.comp f
  have hg : Function.Injective g := positiveEquiv.symm.injective.comp hf
  have h := PaperClaims.positive_geometric_conclusions.2
  exact isSqrtThreeIsomorphicToL2_of_hilbert_equiv PaperClaims.positiveXYHilbertEquiv
    (g ∘ X.independentRows)
    (X.independentRows_linearIndependent.map' g (LinearMap.ker_eq_bot.mpr hg))
    h.2.2.2.1 h.2.2.2.2

theorem xy_positive_isomorphic_l2 : Nonempty (XYPositiveSpace ≃L[ℝ] HalfGraph.RealL2) := by
  obtain ⟨J, _⟩ := xy_positive_sqrtThree_isomorphic_l2
  exact ⟨J⟩
end XY

namespace X.BallLanguage.SeparableHilbertianNormAddIPModel

theorem sqrtThree_isomorphic_l2 (M : SeparableHilbertianNormAddIPModel) :
    IsSqrtThreeIsomorphicToL2 M.model.CompletedDirectedPoint := by
  letI : SeparableSpace M.model.AuxiliaryHilbertCarrier := M.auxiliaryHilbertSeparable
  exact isSqrtThreeIsomorphicToL2_of_hilbert_equiv M.continuousLinearEquivHilbert
    (M.elementaryCopy.embedding ∘ X.independentRows)
    (X.independentRows_linearIndependent.map' M.elementaryCopy.embedding.toLinearMap
      (LinearMap.ker_eq_bot.mpr M.elementaryCopy.embedding.injective))
    M.norm_continuousLinearEquivHilbert_le M.norm_continuousLinearEquivHilbert_symm_le

theorem isomorphic_l2 (M : SeparableHilbertianNormAddIPModel) :
    Nonempty (M.model.CompletedDirectedPoint ≃L[ℝ] HalfGraph.RealL2) := by
  obtain ⟨J, _⟩ := M.sqrtThree_isomorphic_l2
  exact ⟨J⟩
end X.BallLanguage.SeparableHilbertianNormAddIPModel

/-- The geometry of the standard `ℓ₂` example in Table 1. -/
theorem PaperClaims.l2_table_geometry :
    SeparableSpace HalfGraph.RealL2 ∧ PaperClaims.MidpointEstimate HalfGraph.RealL2 ∧
      IsSqrtThreeIsomorphicToL2 HalfGraph.RealL2 := by
  refine ⟨inferInstance, ?_, ?_⟩
  · intro x y hx hy
    rw [norm_midpoint_sq_eq]
    nlinarith [mul_nonneg (norm_nonneg x) (sub_nonneg.mpr hx),
      mul_nonneg (norm_nonneg y) (sub_nonneg.mpr hy), sq_nonneg ‖x - y‖]
  · refine ⟨ContinuousLinearEquiv.refl ℝ HalfGraph.RealL2, ?_⟩
    change ‖ContinuousLinearMap.id ℝ HalfGraph.RealL2‖ *
      ‖ContinuousLinearMap.id ℝ HalfGraph.RealL2‖ ≤ Real.sqrt 3
    calc
      _ ≤ 1 * 1 := mul_le_mul ContinuousLinearMap.norm_id_le ContinuousLinearMap.norm_id_le
        (norm_nonneg _) (zero_le_one' ℝ)
      _ ≤ Real.sqrt 3 := by norm_num

end
end NormFormula
