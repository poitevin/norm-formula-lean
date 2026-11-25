import NormFormula.Analytic.AugmentedNorm
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-! # A dominating seminorm as the actual norm of a new space -/
namespace NormFormula
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure SeminormRenorm (N : Seminorm ℝ E) (lower : ∀ x, ‖x‖ ≤ N x) where
  val : E

namespace SeminormRenorm
variable (N : Seminorm ℝ E) (lower : ∀ x, ‖x‖ ≤ N x)

def equiv : SeminormRenorm N lower ≃ E := ⟨val, SeminormRenorm.mk, fun _ ↦ rfl, fun _ ↦ rfl⟩
instance : AddCommGroup (SeminormRenorm N lower) := (equiv N lower).addCommGroup
instance : Module ℝ (SeminormRenorm N lower) := (equiv N lower).module ℝ
instance : Norm (SeminormRenorm N lower) := ⟨fun x ↦ N x.val⟩
private def core : NormedSpace.Core ℝ (SeminormRenorm N lower) where
  norm_nonneg x := apply_nonneg N x.val
  norm_smul r x := map_smul_eq_mul N r x.val
  norm_triangle x y := map_add_le_add N x.val y.val
  norm_eq_zero_iff x := by
    constructor
    · intro h
      apply (equiv N lower).injective
      exact norm_eq_zero.mp (le_antisymm ((lower x.val).trans_eq h) (norm_nonneg _))
    · rintro rfl
      exact map_zero N
instance : NormedAddCommGroup (SeminormRenorm N lower) := NormedAddCommGroup.ofCore (core N lower)
instance : NormedSpace ℝ (SeminormRenorm N lower) := NormedSpace.ofCore (core N lower)

def linearEquiv : SeminormRenorm N lower ≃ₗ[ℝ] E where
  toEquiv := equiv N lower
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem norm_mk (x : E) : ‖(⟨x⟩ : SeminormRenorm N lower)‖ = N x := rfl
@[simp] theorem val_add (x y : SeminormRenorm N lower) : (x+y).val = x.val+y.val := rfl
@[simp] theorem val_smul (r : ℝ) (x : SeminormRenorm N lower) : (r • x).val = r • x.val := rfl

def continuousLinearEquiv (C : ℝ) (upper : ∀ x, N x ≤ C*‖x‖) :
    SeminormRenorm N lower ≃L[ℝ] E :=
  (linearEquiv N lower).toContinuousLinearEquivOfBounds 1 C
    (fun x ↦ by simpa using lower x.val) upper

theorem completeSpace [CompleteSpace E] (C : ℝ) (upper : ∀ x, N x ≤ C*‖x‖) :
    CompleteSpace (SeminormRenorm N lower) :=
  (completeSpace_congr (continuousLinearEquiv N lower C upper).isUniformEmbedding).mpr inferInstance

theorem separableSpace [TopologicalSpace.SeparableSpace E]
    (C : ℝ) (upper : ∀ x, N x ≤ C*‖x‖) :
    TopologicalSpace.SeparableSpace (SeminormRenorm N lower) := by
  let e := (continuousLinearEquiv N lower C upper).symm.toHomeomorph
  have h := TopologicalSpace.isSeparable_range e.continuous
  rw [e.surjective.range_eq] at h
  exact TopologicalSpace.isSeparable_univ_iff.mp h
end SeminormRenorm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

abbrev AugmentedSpace (p : Seminorm ℝ H) :=
  SeminormRenorm (augmentedSeminorm p) (norm_le_augmentedNorm p)

namespace AugmentedSpace
variable (p : Seminorm ℝ H)

def linearEquiv : AugmentedSpace p ≃ₗ[ℝ] H :=
  SeminormRenorm.linearEquiv _ _

theorem hilbert_le (x : AugmentedSpace p) : ‖linearEquiv p x‖ ≤ ‖x‖ :=
  norm_le_augmentedNorm p x.val

theorem seminorm_le (x : AugmentedSpace p) : p (linearEquiv p x) ≤ ‖x‖ :=
  seminorm_le_augmentedNorm p x.val

theorem upper {C : ℝ} (hC : 0 ≤ C) (hp : ∀ x, p x ≤ C*‖x‖) (x : H) :
    augmentedNorm p x ≤ Real.sqrt (1+C^2)*‖x‖ := by
  apply (sq_le_sq₀ (augmentedNorm_nonneg p x) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [augmentedNorm_sq, mul_pow, Real.sq_sqrt (by positivity)]
  have h := (sq_le_sq₀ (apply_nonneg p x) (mul_nonneg hC (norm_nonneg x))).mpr (hp x)
  nlinarith

end AugmentedSpace
end
end NormFormula
