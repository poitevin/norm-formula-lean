import NormFormula.ModelTheory.BoundedStability
import Mathlib.Topology.Instances.RealVectorSpace

/-! # Stability of arbitrary countable sums of finite-dimensional spaces

Compactness of the product of coordinate balls supplies the subsequence
used in the paper's Pythagorean calculation. Finite partial sums show that
its limit belongs to the same bounded ball of the sum. The calculation only
needs coordinatewise convergence, so no uniform Hilbert comparison is used.
-/

namespace NormFormula
noncomputable section
open Filter
open scoped Topology

variable {E : ℕ → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]

theorem l2Sum_coordinatewise_subsequence (z : ℕ → lp E 2) (C : ℝ)
    (hz : ∀ n, ‖z n‖ ≤ C) :
    ∃ x : lp E 2, ‖x‖ ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, Tendsto (fun n ↦ z (φ n) i) atTop (𝓝 (x i)) := by
  have hC : 0 ≤ C := (norm_nonneg (z 0)).trans (hz 0)
  let K (i : ℕ) := Metric.closedBall (0 : E i) C
  letI (i : ℕ) : CompactSpace (K i) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E i) C)
  let points (n : ℕ) (i : ℕ) : K i :=
    ⟨z n i, by simpa only [K, Metric.mem_closedBall, dist_zero_right] using
      (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (z n) i).trans (hz n)⟩
  obtain ⟨a, φ, hφ, ha⟩ := CompactSpace.tendsto_subseq points
  have hcoord (i : ℕ) : Tendsto (fun n ↦ z (φ n) i) atTop (𝓝 (a i).1) :=
    continuous_subtype_val.continuousAt.tendsto.comp ((tendsto_pi_nhds.mp ha) i)
  have hsum (s : Finset ℕ) : ∑ i ∈ s, ‖(a i).1‖ ^ 2 ≤ C ^ 2 := by
    apply le_of_tendsto (tendsto_finset_sum s fun i _ ↦ (hcoord i).norm.pow 2)
    apply Eventually.of_forall
    intro n
    have h := lp.sum_rpow_le_norm_rpow (p := (2 : ENNReal)) (by norm_num) (z (φ n)) s
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
    exact h.trans ((sq_le_sq₀ (norm_nonneg _) hC).mpr (hz (φ n)))
  have hmem : Memℓp (fun i ↦ (a i).1) 2 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      summable_of_sum_le (fun _ ↦ sq_nonneg _) hsum
  let x : lp E 2 := ⟨fun i ↦ (a i).1, hmem⟩
  refine ⟨x, ?_, φ, hφ, hcoord⟩
  apply lp.norm_le_of_forall_sum_le (by norm_num) hC
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hsum

theorem l2Sum_prepared_subsequence (z : ℕ → lp E 2) (C : ℝ)
    (hz : ∀ n, ‖z n‖ ≤ C) :
    ∃ x : lp E 2, ∃ φ : ℕ → ℕ, ∃ a : ℝ,
      StrictMono φ ∧ (∀ i, Tendsto (fun n ↦ z (φ n) i) atTop (𝓝 (x i))) ∧
      Tendsto (fun n ↦ ‖z (φ n) - x‖) atTop (𝓝 a) ∧
      ∀ n, ‖z (φ n) - x‖ ≤ C + ‖x‖ := by
  obtain ⟨x, _, φ, hφ, hcoord⟩ := l2Sum_coordinatewise_subsequence z C hz
  have hb (n : ℕ) : ‖z (φ n) - x‖ ≤ C + ‖x‖ :=
    (norm_sub_le _ _).trans (add_le_add (hz _) le_rfl)
  obtain ⟨a, _, ψ, hψ, hnorm⟩ := isCompact_Icc.tendsto_subseq
    (fun n ↦ (⟨norm_nonneg _, hb n⟩ : ‖z (φ n) - x‖ ∈ Set.Icc 0 (C + ‖x‖)))
  exact ⟨x, φ ∘ ψ, a, hφ.comp hψ,
    fun i ↦ (hcoord i).comp hψ.tendsto_atTop, hnorm, fun n ↦ hb (ψ n)⟩

omit [∀ i, NormedSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)] in
theorem tendsto_norm_add_sq_of_coordinatewise_limit
    (u : lp E 2) {z : ℕ → lp E 2} {x : lp E 2} {C a : ℝ}
    (hcoord : ∀ i, Tendsto (fun n ↦ z n i) atTop (𝓝 (x i)))
    (hbound : ∀ n, ‖z n - x‖ ≤ C)
    (hnorm : Tendsto (fun n ↦ ‖z n - x‖) atTop (𝓝 a)) :
    Tendsto (fun n ↦ ‖u + z n‖ ^ 2) atTop (𝓝 (‖u + x‖ ^ 2 + a ^ 2)) := by
  have hzero (i : ℕ) : Tendsto (fun n ↦ ‖(z n - x) i‖) atTop (𝓝 0) := by
    simpa only [lp.coeFn_sub, Pi.sub_apply, sub_self, norm_zero] using
      ((hcoord i).sub_const (x i)).norm
  have h := tendsto_norm_add_sq_of_coordinatewise (u + x) hbound hzero hnorm
  simpa only [add_add_sub_cancel] using h

/-- The paper's general stability theorem, without a compactness premise or
a uniform Hilbert distortion assumption. -/
theorem l2Sum_norm_isStableOnBounded :
    IsStableOnBounded (fun x y : lp E 2 ↦ ‖x + y‖) := by
  intro xs ys C D first second hxs hys hfirst hsecond
  obtain ⟨x, φ, a, hφ, hx, hxa, hxb⟩ := l2Sum_prepared_subsequence xs C hxs
  obtain ⟨y, ψ, b, hψ, hy, hyb, hyc⟩ := l2Sum_prepared_subsequence ys D hys
  have hunsq {v : ℕ → ℝ} {L : ℝ} (hv : ∀ n, 0 ≤ v n)
      (h : Tendsto (fun n ↦ v n ^ 2) atTop (𝓝 L)) :
      Tendsto v atTop (𝓝 (Real.sqrt L)) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (hv _)] using Real.continuous_sqrt.continuousAt.tendsto.comp h
  have hinner (m : ℕ) := hunsq (fun n ↦ norm_nonneg (xs (φ m) + ys (ψ n)))
    (tendsto_norm_add_sq_of_coordinatewise_limit (xs (φ m)) hy hyc hyb)
  have houter := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((tendsto_norm_add_sq_of_coordinatewise_limit y hx hxb hxa).add_const (b ^ 2))
  have hforward : HasSuccessiveLimit (fun m n ↦ ‖xs (φ m) + ys (ψ n)‖)
      (Real.sqrt (‖x + y‖ ^ 2 + a ^ 2 + b ^ 2)) := by
    refine ⟨fun m ↦ Real.sqrt (‖xs (φ m) + y‖ ^ 2 + b ^ 2), hinner, ?_⟩
    simpa only [add_comm y] using houter
  have hinner' (n : ℕ) := hunsq (fun m ↦ norm_nonneg (ys (ψ n) + xs (φ m)))
    (tendsto_norm_add_sq_of_coordinatewise_limit (ys (ψ n)) hx hxb hxa)
  have houter' := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((tendsto_norm_add_sq_of_coordinatewise_limit x hy hyc hyb).add_const (a ^ 2))
  have hbackward : HasSuccessiveLimit (fun n m ↦ ‖xs (φ m) + ys (ψ n)‖)
      (Real.sqrt (‖x + y‖ ^ 2 + a ^ 2 + b ^ 2)) := by
    refine ⟨fun n ↦ Real.sqrt (‖x + ys (ψ n)‖ ^ 2 + a ^ 2), ?_, ?_⟩
    · intro n
      simpa only [add_comm] using hinner' n
    · simpa only [add_right_comm _ (b ^ 2)] using houter'
  exact ((hfirst.subseq hφ hψ).unique hforward).trans
    ((hsecond.subseq hψ hφ).unique hbackward).symm

end
end NormFormula
