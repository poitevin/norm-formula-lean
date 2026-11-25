import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.WeakDual
import NormFormula.ModelTheory.BoundedStability

/-! # Stability of real Hilbert norm translations -/
namespace NormFormula
noncomputable section
open Filter TopologicalSpace
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section Separable
variable [SeparableSpace H]

/-- A Hilbert vector regarded, by the Riesz representation theorem, as an
element of the weak-star dual. -/
def rieszWeakDual (x : H) : WeakDual ℝ H :=
  StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H x)

/-- Every bounded sequence in the Hilbert model has a weakly convergent
subsequence.  This is sequential Banach--Alaoglu transported through the
Riesz representation theorem. -/
theorem hilbert_weakSequentialCompactnessOnBounded :
    WeakSequentialCompactnessOnBounded H := by
  intro z C hz
  have hzmem (n : ℕ) : rieszWeakDual (z n) ∈
      WeakDual.toStrongDual ⁻¹' Metric.closedBall
        (0 : StrongDual ℝ H) C := by
    change dist (InnerProductSpace.toDual ℝ H (z n)) 0 ≤ C
    simpa [dist_zero_right] using hz n
  obtain ⟨w, hw, φ, hφ, hφWeakDual⟩ :=
    (WeakDual.isSeqCompact_closedBall ℝ H
      (0 : StrongDual ℝ H) C) hzmem
  let x : H :=
    (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual w)
  refine ⟨x, φ, hφ, ?_⟩
  unfold WeaklyTendsto
  have hinj : Function.Injective (topDualPairing ℝ H).flip := by
    intro u v huv
    apply (NormedSpace.inclusionInDoubleDualLi ℝ).injective
    ext g
    exact DFunLike.congr_fun huv g
  refine (WeakBilin.tendsto_iff_forall_eval_tendsto
    (B := (topDualPairing ℝ H).flip) hinj).2 ?_
  intro g
  have heval :=
    (tendsto_iff_forall_eval_tendsto_topDualPairing.mp hφWeakDual)
      ((InnerProductSpace.toDual ℝ H).symm g)
  convert heval using 1
  · ext i
    change g (z (φ i)) = inner ℝ (z (φ i))
      ((InnerProductSpace.toDual ℝ H).symm g)
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  · congr 1
    change g x = w ((InnerProductSpace.toDual ℝ H).symm g)
    rw [← WeakDual.toStrongDual_apply]
    change g ((InnerProductSpace.toDual ℝ H).symm
      (WeakDual.toStrongDual w)) =
        WeakDual.toStrongDual w ((InnerProductSpace.toDual ℝ H).symm g)
    rw [← InnerProductSpace.toDual_symm_apply]
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]


end Separable

/-- Weak convergence controls the cross term in the Hilbert norm square. -/
theorem hilbert_tendsto_norm_add_sq
    (u : H) {z : ℕ → H} {x : H} {a : ℝ}
    (hz : WeaklyTendsto z atTop x)
    (ha : Tendsto (fun n ↦ ‖z n - x‖) atTop (𝓝 a)) :
    Tendsto (fun n ↦ ‖u + z n‖ ^ 2) atTop (𝓝 (‖u + x‖ ^ 2 + a ^ 2)) := by
  have hweak := hz.isWeaklyNull_sub
  have hinner := (hweak.map (InnerProductSpace.toDual ℝ H (u + x))).tendsto_of_finiteDimensional
  have hzero : Tendsto (fun n ↦ inner ℝ (u + x) (z n - x)) atTop (𝓝 0) := by
    simpa only [map_zero] using hinner
  have h := ((tendsto_const_nhds (x := ‖u + x‖ ^ 2)).add (hzero.const_mul 2)).add (ha.pow 2)
  convert h using 1
  · funext n
    rw [← norm_add_sq_real]
    congr 2
    abel
  · simp

section Separable
variable [SeparableSpace H]

theorem hilbert_norm_isStableOnBounded_separable :
    IsStableOnBounded (fun x y : H ↦ ‖x + y‖) := by
  intro xs ys C D first second hxs hys hfirst hsecond
  obtain ⟨x, φ, a, hφ, hx, hxa, _⟩ :=
    hilbert_weakSequentialCompactnessOnBounded.exists_prepared_subsequence xs C hxs
  obtain ⟨y, ψ, b, hψ, hy, hyb, _⟩ :=
    hilbert_weakSequentialCompactnessOnBounded.exists_prepared_subsequence ys D hys
  have hunsq {v : ℕ → ℝ} {L : ℝ} (hv : ∀ n, 0 ≤ v n)
      (h : Tendsto (fun n ↦ v n ^ 2) atTop (𝓝 L)) :
      Tendsto v atTop (𝓝 (Real.sqrt L)) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (hv _)] using
      Real.continuous_sqrt.continuousAt.tendsto.comp h
  have hinner (m : ℕ) := hunsq (fun n ↦ norm_nonneg (xs (φ m) + ys (ψ n)))
    (hilbert_tendsto_norm_add_sq (xs (φ m)) hy hyb)
  have houter := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((hilbert_tendsto_norm_add_sq y hx hxa).add_const (b ^ 2))
  have hforward : HasSuccessiveLimit (fun m n ↦ ‖xs (φ m) + ys (ψ n)‖)
      (Real.sqrt (‖x + y‖ ^ 2 + a ^ 2 + b ^ 2)) := by
    refine ⟨fun m ↦ Real.sqrt (‖xs (φ m) + y‖ ^ 2 + b ^ 2), hinner, ?_⟩
    simpa only [add_comm y] using houter
  have hinner' (n : ℕ) := hunsq (fun m ↦ norm_nonneg (ys (ψ n) + xs (φ m)))
    (hilbert_tendsto_norm_add_sq (ys (ψ n)) hx hxa)
  have houter' := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((hilbert_tendsto_norm_add_sq x hy hyb).add_const (a ^ 2))
  have hbackward : HasSuccessiveLimit (fun n m ↦ ‖xs (φ m) + ys (ψ n)‖)
      (Real.sqrt (‖x + y‖ ^ 2 + a ^ 2 + b ^ 2)) := by
    refine ⟨fun n ↦ Real.sqrt (‖x + ys (ψ n)‖ ^ 2 + a ^ 2), ?_, ?_⟩
    · intro n
      simpa only [add_comm] using hinner' n
    · simpa only [add_right_comm _ (b ^ 2)] using houter'
  exact ((hfirst.subseq hφ hψ).unique hforward).trans
    ((hsecond.subseq hψ hφ).unique hbackward).symm
end Separable

/-- Restricting two sequences to their separable closed linear span proves
stability in an arbitrary real Hilbert space. -/
theorem hilbert_norm_isStableOnBounded :
    IsStableOnBounded (fun x y : H ↦ ‖x + y‖) := by
  intro xs ys C D first second hxs hys hfirst hsecond
  let S := (Submodule.span ℝ (Set.range xs ∪ Set.range ys)).topologicalClosure
  have hsep : IsSeparable (S : Set H) :=
    ((Set.countable_range xs).union (Set.countable_range ys)).isSeparable.span.closure
  letI : NormedAddCommGroup S := inferInstance
  letI : InnerProductSpace ℝ S := inferInstance
  letI : SeparableSpace S := hsep.separableSpace
  letI : CompleteSpace S := (show IsClosed (S : Set H) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let xs' (n : ℕ) : S := ⟨xs n, Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_union_left _ (Set.mem_range_self n)))⟩
  let ys' (n : ℕ) : S := ⟨ys n, Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_union_right _ (Set.mem_range_self n)))⟩
  exact @hilbert_norm_isStableOnBounded_separable S _ _ ‹CompleteSpace S› ‹SeparableSpace S› xs' ys' C D first second
    hxs hys hfirst hsecond

end
end NormFormula
