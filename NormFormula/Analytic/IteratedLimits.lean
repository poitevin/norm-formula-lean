import NormFormula.Analytic.WeakL2Sum

/-!
# Translated weak limits and the double-limit calculation

This file packages the next analytic step in the paper's local-stability
argument.  A weakly convergent sequence is translated by its weak limit to
produce a weakly null difference sequence.  Asymptotic Pythagoras then gives
the norm limit for translates of the original sequence.  Applying this to two
sequences verifies that the two successive limit calculations have the same
explicit Pythagorean value.
-/

namespace NormFormula

noncomputable section

open Filter
open scoped Topology

/-- Subtracting a constant preserves weak convergence and subtracts it from
the weak limit. -/
theorem WeaklyTendsto.sub_const
    {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {z : α → E} {l : Filter α} {x : E} (h : WeaklyTendsto z l x) (y : E) :
    WeaklyTendsto (fun a ↦ z a - y) l (x - y) := by
  unfold WeaklyTendsto at h ⊢
  have hy : Tendsto (fun _ : α ↦ toWeakSpace ℝ E y) l
      (𝓝 (toWeakSpace ℝ E y)) := tendsto_const_nhds
  simpa using h.sub hy

/-- Translating a weakly convergent sequence by its limit produces a weakly
null sequence. -/
theorem WeaklyTendsto.isWeaklyNull_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {z : ℕ → E} {x : E} (h : WeaklyTendsto z atTop x) :
    IsWeaklyNull (fun m ↦ z m - x) := by
  simpa [IsWeaklyNull] using h.sub_const x

section L2Sum

variable {ι : Type*} {E : ι → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
variable [∀ i, FiniteDimensional ℝ (E i)] [DecidableEq ι]

/-- Asymptotic Pythagoras translated from a weakly null sequence to a sequence
with an arbitrary weak limit. -/
theorem tendsto_norm_add_sq_of_weaklyTendsto
    (u : lp E 2) {z : ℕ → lp E 2} {x : lp E 2} {C limit : ℝ}
    (hzWeak : WeaklyTendsto z atTop x)
    (hzBounded : ∀ m, ‖z m - x‖ ≤ C)
    (hzNorm : Tendsto (fun m ↦ ‖z m - x‖) atTop (𝓝 limit)) :
    Tendsto (fun m ↦ ‖u + z m‖ ^ 2) atTop
      (𝓝 (‖u + x‖ ^ 2 + limit ^ 2)) := by
  have hp := tendsto_norm_add_sq_of_weaklyNull (u + x)
    hzWeak.isWeaklyNull_sub hzBounded hzNorm
  have hadd (m : ℕ) : (u + x) + (z m - x) = u + z m := by abel
  simpa only [hadd] using hp

/-- The corresponding, unsquared norm limit. -/
theorem tendsto_norm_add_of_weaklyTendsto
    (u : lp E 2) {z : ℕ → lp E 2} {x : lp E 2} {C limit : ℝ}
    (hzWeak : WeaklyTendsto z atTop x)
    (hzBounded : ∀ m, ‖z m - x‖ ≤ C)
    (hzNorm : Tendsto (fun m ↦ ‖z m - x‖) atTop (𝓝 limit)) :
    Tendsto (fun m ↦ ‖u + z m‖) atTop
      (𝓝 (Real.sqrt (‖u + x‖ ^ 2 + limit ^ 2))) := by
  have hsq := tendsto_norm_add_sq_of_weaklyTendsto u hzWeak hzBounded hzNorm
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  change Tendsto (fun m ↦ Real.sqrt (‖u + z m‖ ^ 2)) atTop
    (𝓝 (Real.sqrt (‖u + x‖ ^ 2 + limit ^ 2))) at hsqrt
  simpa only [Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using hsqrt


end L2Sum

namespace X


end X

end

end NormFormula
