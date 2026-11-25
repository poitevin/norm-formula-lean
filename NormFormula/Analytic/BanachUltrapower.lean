import NormFormula.ContinuousLogic.UltralimitAlong
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.OfNorm

/-! # Banach ultrapowers along arbitrary ultrafilters

The norm of a bounded family is the ultralimit of its coordinate norms.
The completion separates the resulting seminorm and completes the quotient.
For Hilbert spaces the parallelogram identity passes to this norm.
-/

namespace NormFormula
noncomputable section
open Filter
open scoped Topology ENNReal
open ContinuousLogic

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def ultraNormTruth (x : lp (fun _ : ι ↦ E) ∞) (i : ι) : TruthValue :=
  ⟨‖x i‖ / (‖x‖ + 1), div_nonneg (norm_nonneg _) (by positivity),
    (div_le_one (by positivity)).mpr
      ((lp.norm_apply_le_norm (by simp) x i).trans (by linarith))⟩

def ultraNorm (U : Ultrafilter ι) (x : lp (fun _ : ι ↦ E) ∞) : ℝ :=
  (‖x‖ + 1) * (ultralimitAlong U (ultraNormTruth x) : ℝ)

omit [NormedSpace ℝ E] in
theorem tendsto_ultraNorm (U : Ultrafilter ι) (x : lp (fun _ : ι ↦ E) ∞) :
    Tendsto (fun i ↦ ‖x i‖) U (𝓝 (ultraNorm U x)) := by
  have h := (tendsto_const_nhds (x := ‖x‖ + 1)).mul
    (continuous_subtype_val.continuousAt.tendsto.comp
      (tendsto_ultralimitAlong U (ultraNormTruth x)))
  convert h using 1
  funext i
  change ‖x i‖ = (‖x‖ + 1) * (‖x i‖ / (‖x‖ + 1))
  field_simp

def ultraSeminorm (U : Ultrafilter ι) : Seminorm ℝ (lp (fun _ : ι ↦ E) ∞) :=
  Seminorm.of (ultraNorm U)
    (fun x y ↦ le_of_tendsto_of_tendsto (tendsto_ultraNorm U (x + y))
      ((tendsto_ultraNorm U x).add (tendsto_ultraNorm U y))
      (Eventually.of_forall fun i ↦ norm_add_le (x i) (y i)))
    (fun r x ↦ tendsto_nhds_unique (tendsto_ultraNorm U (r • x))
      (by simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul] using
        (tendsto_ultraNorm U x).const_mul ‖r‖))

structure UltraSequence (U : Ultrafilter ι) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  bounded : lp (fun _ : ι ↦ E) ∞

namespace UltraSequence
variable (U : Ultrafilter ι)

def equiv : UltraSequence U E ≃ lp (fun _ : ι ↦ E) ∞ :=
  ⟨bounded, UltraSequence.mk, fun _ ↦ rfl, fun _ ↦ rfl⟩
instance : AddCommGroup (UltraSequence U E) := (equiv U).addCommGroup
instance : Module ℝ (UltraSequence U E) := (equiv U).module ℝ
def linearEquiv : UltraSequence U E ≃ₗ[ℝ] lp (fun _ : ι ↦ E) ∞ where
  toEquiv := equiv U
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def seminorm : Seminorm ℝ (UltraSequence U E) :=
  (ultraSeminorm U).comp (linearEquiv U).toLinearMap
instance : SeminormedAddCommGroup (UltraSequence U E) :=
  (seminorm U).toAddGroupSeminorm.toSeminormedAddCommGroup
instance : NormedSpace ℝ (UltraSequence U E) where
  norm_smul_le r x := (map_smul_eq_mul (seminorm U) r x).le

theorem tendsto_norm (x : UltraSequence U E) :
    Tendsto (fun i ↦ ‖x.bounded i‖) U (𝓝 ‖x‖) := tendsto_ultraNorm U x.bounded

end UltraSequence

abbrev BanachUltrapower (U : Ultrafilter ι) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  UniformSpace.Completion (UltraSequence U E)

namespace BanachUltrapower
variable (U : Ultrafilter ι)

def ofBounded (x : lp (fun _ : ι ↦ E) ∞) : BanachUltrapower U E :=
  (⟨x⟩ : UltraSequence U E)

theorem norm_ofBounded (x : lp (fun _ : ι ↦ E) ∞) :
    ‖ofBounded U x‖ = ultraNorm U x := UniformSpace.Completion.norm_coe _

theorem tendsto_norm_ofBounded (x : lp (fun _ : ι ↦ E) ∞) :
    Tendsto (fun i ↦ ‖x i‖) U (𝓝 ‖ofBounded U x‖) := by
  rw [norm_ofBounded]
  exact tendsto_ultraNorm U x

@[simp] theorem ofBounded_add (x y : lp (fun _ : ι ↦ E) ∞) :
    ofBounded U (x + y) = ofBounded U x + ofBounded U y :=
  UniformSpace.Completion.coe_add _ _

@[simp] theorem ofBounded_smul (r : ℝ) (x : lp (fun _ : ι ↦ E) ∞) :
    ofBounded U (r • x) = r • ofBounded U x :=
  UniformSpace.Completion.coe_smul r _

theorem norm_ofBounded_le (x : lp (fun _ : ι ↦ E) ∞) {C : ℝ}
    (hx : ∀ᶠ i in U, ‖x i‖ ≤ C) : ‖ofBounded U x‖ ≤ C :=
  le_of_tendsto (tendsto_norm_ofBounded U x) hx


/-- A uniformly bounded family, as an element of `ℓ∞`. -/
def boundedFamily (f : ι → E) (C : ℝ) (hf : ∀ i, ‖f i‖ ≤ C) :
    lp (fun _ : ι ↦ E) ∞ :=
  ⟨f, memℓp_infty ⟨C, by rintro _ ⟨i, rfl⟩; exact hf i⟩⟩

omit [NormedSpace ℝ E] in
@[simp] theorem boundedFamily_apply (f : ι → E) (C : ℝ)
    (hf : ∀ i, ‖f i‖ ≤ C) (i : ι) : boundedFamily f C hf i = f i := rfl

/-- The parallelogram law passes through the ultralimit and completion. -/
theorem parallelogram [InnerProductSpace ℝ E] (x y : BanachUltrapower U E) :
    ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ =
      2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a b
  simp only [← UniformSpace.Completion.coe_add, ← UniformSpace.Completion.coe_sub,
    UniformSpace.Completion.norm_coe]
  have hleft := ((UltraSequence.tendsto_norm U (a + b)).mul
    (UltraSequence.tendsto_norm U (a + b))).add
    ((UltraSequence.tendsto_norm U (a - b)).mul (UltraSequence.tendsto_norm U (a - b)))
  have hright := (((UltraSequence.tendsto_norm U a).mul (UltraSequence.tendsto_norm U a)).add
    ((UltraSequence.tendsto_norm U b).mul (UltraSequence.tendsto_norm U b))).const_mul 2
  apply tendsto_nhds_unique hleft
  convert hright using 1
  funext i
  simpa only [pow_two] using parallelogram_law_with_norm ℝ (a.bounded i) (b.bounded i)

instance [InnerProductSpace ℝ E] : InnerProductSpace ℝ (BanachUltrapower U E) :=
  InnerProductSpace.ofNorm ℝ (parallelogram U)

end BanachUltrapower
end
end NormFormula
