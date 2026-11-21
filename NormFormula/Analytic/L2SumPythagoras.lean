import NormFormula.Analytic.L2SumDefect

/-!
# Asymptotic Pythagoras for dependent `ℓ₂`-sums

This file proves the analytic core of the paper's asymptotic Pythagoras lemma.
A bounded sequence in a dependent `ℓ₂`-sum has vanishing norm-square defect
against every fixed vector whenever the norm of each coordinate tends to zero.
If the norms of the sequence also converge, the asserted Pythagorean limit
follows.

The later weak-convergence bridge only has to show coordinatewise norm
convergence; finite dimensionality of the summands is not needed here.
-/

namespace NormFormula

noncomputable section

open Filter
open scoped Topology

/-- If the norm of the second vector tends to zero, then its norm-square defect
against a fixed vector tends to zero in every normed space. -/
theorem tendsto_normSqDefect_zero_of_tendsto_norm
    {α E : Type*} [NormedAddCommGroup E] {l : Filter α} (u : E)
    {v : α → E} (hv : Tendsto (fun a ↦ ‖v a‖) l (𝓝 0)) :
    Tendsto (fun a ↦ normSqDefect u (v a)) l (𝓝 0) := by
  have hbound : Tendsto (fun a ↦ 2 * ‖u‖ * ‖v a‖) l (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hv
  have hneg : Tendsto (fun a ↦ -(2 * ‖u‖ * ‖v a‖)) l (𝓝 0) := by
    simpa using hbound.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hbound
  · filter_upwards with a
    exact le_trans (neg_le_neg (abs_normSqDefect_le u (v a))) (neg_abs_le _)
  · filter_upwards with a
    exact le_trans (le_abs_self _) (abs_normSqDefect_le u (v a))

section L2Sum

variable {ι : Type*} {E : ι → Type*}
variable [∀ i, NormedAddCommGroup (E i)]
variable [DecidableEq ι]

/-- Removing finitely many coordinates cannot increase the `ℓ₂` norm. -/
theorem norm_lpTail_le (s : Finset ι) (f : lp E 2) :
    ‖lpTail s f‖ ≤ ‖f‖ := by
  have hsum : 0 ≤ ∑ i ∈ s, ‖f i‖ ^ 2 := by
    exact Finset.sum_nonneg fun i _ ↦ sq_nonneg ‖f i‖
  have hsq : ‖lpTail s f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [norm_lpTail_sq]
    linarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- A bounded coordinatewise-null sequence has asymptotically zero
norm-square defect against every fixed vector. -/
theorem tendsto_normSqDefect_of_coordinatewise
    (u : lp E 2) {z : ℕ → lp E 2} {C : ℝ}
    (hzBounded : ∀ m, ‖z m‖ ≤ C)
    (hzCoord : ∀ i, Tendsto (fun m ↦ ‖z m i‖) atTop (𝓝 0)) :
    Tendsto (fun m ↦ normSqDefect u (z m)) atTop (𝓝 0) := by
  have hC : 0 ≤ C :=
    le_trans (norm_nonneg (z 0)) (hzBounded 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε / (4 * (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hsEventually : ∀ᶠ s : Finset ι in atTop, ‖lpTail s u‖ < δ :=
    (tendsto_order.1 (tendsto_norm_lpTail_zero u)).2 δ hδ
  obtain ⟨s, hs⟩ := eventually_atTop.1 hsEventually
  have hsu : ‖lpTail s u‖ < δ := hs s le_rfl
  have hhead : Tendsto
      (fun m ↦ ∑ i ∈ s, normSqDefect (u i) (z m i)) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum s fun i _ ↦
      tendsto_normSqDefect_zero_of_tendsto_norm (u i) (hzCoord i)
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 hhead) (ε / 2) (by positivity)
  refine ⟨N, fun m hm ↦ ?_⟩
  have hheadAbs :
      |∑ i ∈ s, normSqDefect (u i) (z m i)| < ε / 2 := by
    simpa [Real.dist_eq] using hN m hm
  have htailNorm : ‖lpTail s (z m)‖ ≤ C :=
    le_trans (norm_lpTail_le s (z m)) (hzBounded m)
  have htailAbs :
      |normSqDefect (lpTail s u) (lpTail s (z m))| < ε / 2 := by
    calc
      |normSqDefect (lpTail s u) (lpTail s (z m))| ≤
          2 * ‖lpTail s u‖ * ‖lpTail s (z m)‖ :=
        abs_normSqDefect_le _ _
      _ ≤ 2 * ‖lpTail s u‖ * C :=
        mul_le_mul_of_nonneg_left htailNorm (by positivity)
      _ ≤ 2 * ‖lpTail s u‖ * (C + 1) := by
        gcongr
        linarith
      _ = (2 * (C + 1)) * ‖lpTail s u‖ := by ring
      _ < (2 * (C + 1)) * δ :=
        mul_lt_mul_of_pos_left hsu (by positivity)
      _ = ε / 2 := by
        dsimp [δ]
        field_simp
        ring
  rw [normSqDefect_eq_sum_add_tail s]
  rw [Real.dist_eq, sub_zero]
  calc
    |(∑ i ∈ s, normSqDefect (u i) (z m i)) +
        normSqDefect (lpTail s u) (lpTail s (z m))| ≤
        |∑ i ∈ s, normSqDefect (u i) (z m i)| +
          |normSqDefect (lpTail s u) (lpTail s (z m))| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hheadAbs htailAbs
    _ = ε := by ring

/-- Asymptotic Pythagoras under the analytic hypotheses: boundedness,
coordinatewise convergence to zero, and convergence of the global norms. -/
theorem tendsto_norm_add_sq_of_coordinatewise
    (u : lp E 2) {z : ℕ → lp E 2} {C limit : ℝ}
    (hzBounded : ∀ m, ‖z m‖ ≤ C)
    (hzCoord : ∀ i, Tendsto (fun m ↦ ‖z m i‖) atTop (𝓝 0))
    (hzNorm : Tendsto (fun m ↦ ‖z m‖) atTop (𝓝 limit)) :
    Tendsto (fun m ↦ ‖u + z m‖ ^ 2) atTop (𝓝 (‖u‖ ^ 2 + limit ^ 2)) := by
  have hdefect := tendsto_normSqDefect_of_coordinatewise u hzBounded hzCoord
  have hconst : Tendsto (fun _ : ℕ ↦ ‖u‖ ^ 2) atTop (𝓝 (‖u‖ ^ 2)) :=
    tendsto_const_nhds
  have hsum := hdefect.add (hconst.add (hzNorm.pow 2))
  convert hsum using 1 <;> simp [normSqDefect]

end L2Sum

end

end NormFormula
