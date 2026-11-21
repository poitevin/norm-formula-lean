import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Sequences

/-!
# The Banach space `c₀` and isomorphic copies

Mathlib does not currently provide a named Banach-space model of `c₀`.  We
therefore define it concretely as the subspace of bounded real sequences that
converge to zero.  A continuous linear map from this space which is bounded
below is exactly the data needed for an isomorphic embedding.

The final theorem will exclude this space directly from the quantitative
Hilbert equivalence, so no abstract reflexive-space interface is needed.
-/

namespace NormFormula

open Filter
open scoped ENNReal Topology

noncomputable section

/-- The ambient Banach space of bounded real sequences. -/
abbrev BoundedScalarSequences := lp (fun _ : ℕ ↦ ℝ) ∞

/-- The linear subspace of bounded scalar sequences converging to zero. -/
def c0Submodule : Submodule ℝ BoundedScalarSequences where
  carrier := {x | Tendsto (fun n : ℕ ↦ x n) atTop (𝓝 0)}
  zero_mem' := by
    simpa only [lp.coeFn_zero, Pi.zero_apply] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  add_mem' := by
    intro x y hx hy
    simpa only [lp.coeFn_add, Pi.add_apply, zero_add] using hx.add hy
  smul_mem' := by
    intro c x hx
    simpa only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_zero] using
      (tendsto_const_nhds.mul hx :
        Tendsto (fun n : ℕ ↦ c * x n) atTop (𝓝 (c * 0)))

/-- The concrete normed-space model of `c₀`. -/
abbrev C0Space : Type := c0Submodule

noncomputable instance instNormedSpaceC0Space : NormedSpace ℝ C0Space :=
  Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) c0Submodule

/-- Specialized operator-norm instance for maps whose domain is `C0Space`. -/
noncomputable instance instNormC0ContinuousLinearMap
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] :
    Norm (C0Space →L[ℝ] E) :=
  @ContinuousLinearMap.hasOpNorm ℝ ℝ C0Space E _ _ _ _ _ _ (RingHom.id ℝ)

/-- Uniform limits of scalar sequences converging to zero still converge to
zero, so `c₀` is closed in `ℓ∞`. -/
theorem isClosed_c0Submodule :
    IsClosed (c0Submodule : Set BoundedScalarSequences) := by
  apply IsSeqClosed.isClosed
  intro u x hu hux
  change Tendsto (fun n : ℕ ↦ x n) atTop (𝓝 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ :=
    (Metric.tendsto_atTop.mp hux) (ε / 2) (div_pos hε (by norm_num))
  have hkx : ‖x - u k‖ < ε / 2 := by
    simpa [dist_eq_norm, norm_sub_rev] using hk k le_rfl
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.mp (hu k)) (ε / 2) (div_pos hε (by norm_num))
  refine ⟨N, fun n hn ↦ ?_⟩
  have hcoord : ‖x n - u k n‖ ≤ ‖x - u k‖ := by
    simpa only [lp.coeFn_sub, Pi.sub_apply] using
      lp.norm_apply_le_norm ENNReal.top_ne_zero (x - u k) n
  have hun : ‖u k n‖ < ε / 2 := by
    simpa [dist_eq_norm] using hN n hn
  have htri : ‖x n‖ ≤ ‖x n - u k n‖ + ‖u k n‖ := by
    calc
      ‖x n‖ = ‖(x n - u k n) + u k n‖ := by ring_nf
      _ ≤ ‖x n - u k n‖ + ‖u k n‖ := norm_add_le _ _
  have : ‖x n‖ < ε := by linarith
  simpa [dist_eq_norm] using this

noncomputable instance : CompleteSpace C0Space :=
  isClosed_c0Submodule.completeSpace_coe

/-- A Banach space contains an isomorphic copy of `c₀` when there is a
continuous linear embedding of the concrete `C0Space` which is bounded below
by a positive constant.  Continuity supplies the upper bound automatically. -/
def ContainsIsomorphicCopyOfC0
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∃ T : C0Space →L[ℝ] E, ∃ c : ℝ,
    0 < c ∧ ∀ x : C0Space, c * ‖x‖ ≤ ‖T x‖

end

end NormFormula
