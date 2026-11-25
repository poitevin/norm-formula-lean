import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.WeakDual
import NormFormula.Analytic.CompactnessBoundary
import NormFormula.Analytic.XHilbertEquiv

/-!
# Weak sequential compactness for `XSpace`

This file discharges the functional-analytic compactness boundary isolated in
`CompactnessBoundary` for the paper's space `XSpace`.

First, finite-coordinate heads show that the Hilbert model `XHilbertSpace` is
separable.  The sequential Banach--Alaoglu theorem is then applied to the
Riesz images of a bounded sequence.  Symmetry of the real inner product turns
the resulting weak-star convergence back into weak convergence in the Hilbert
space.  Finally, the continuous linear equivalence from `XHilbertEquiv`
transfers the subsequence to `XSpace`.
-/

namespace NormFormula.X

noncomputable section

open Filter
open TopologicalSpace
open scoped Topology

/-- Embed the first `k` Hilbert blocks into the full Hilbert `ℓ₂`-sum. -/
def hilbertHeadEmbed (k : ℕ) (v : ∀ i : Fin k, BlockHilbert i) : XHilbertSpace :=
  ∑ i : Fin k, lp.single 2 (i : ℕ) (v i)

/-- The finite-head embedding is continuous. -/
theorem continuous_hilbertHeadEmbed (k : ℕ) : Continuous (hilbertHeadEmbed k) := by
  apply continuous_finset_sum
  intro i hi
  exact (lp.isometry_single (E := fun n : ℕ ↦ BlockHilbert n) (p := (2 : ENNReal))
    (i : ℕ)).continuous.comp (continuous_apply i)

/-- Restricting a Hilbert-sum vector to the first `k` blocks and embedding it
again gives its usual finite head. -/
theorem hilbertHeadEmbed_restrict (k : ℕ) (x : XHilbertSpace) :
    hilbertHeadEmbed k (fun i ↦ x i) = lpHead (Finset.range k) x := by
  simp only [hilbertHeadEmbed, lpHead, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.mp hi]

/-- The union of the ranges of all finite-head embeddings. -/
def finiteHeadRange : Set XHilbertSpace :=
  ⋃ k : ℕ, Set.range (hilbertHeadEmbed k)

/-- Finite-head vectors form a separable subset of the Hilbert sum. -/
theorem isSeparable_finiteHeadRange : IsSeparable finiteHeadRange := by
  exact IsSeparable.iUnion (fun k ↦ isSeparable_range (continuous_hilbertHeadEmbed k))

/-- Finite-head vectors are dense in the Hilbert sum. -/
theorem dense_finiteHeadRange : Dense finiteHeadRange := by
  rw [dense_iff_closure_eq]
  apply Set.Subset.antisymm (closure_minimal (Set.subset_univ _) isClosed_univ)
  intro x hx
  apply mem_closure_of_tendsto ((tendsto_lpHead x).comp tendsto_finset_range)
  filter_upwards with k
  refine Set.mem_iUnion.2 ⟨k, ?_⟩
  exact ⟨fun i ↦ x i, hilbertHeadEmbed_restrict k x⟩

/-- The countable dependent Hilbert sum used to model `XSpace` is separable. -/
noncomputable instance : SeparableSpace XHilbertSpace :=
  dense_finiteHeadRange.isSeparable_iff.mp isSeparable_finiteHeadRange

/-- A Hilbert vector regarded, by the Riesz representation theorem, as an
element of the weak-star dual. -/
def rieszWeakDual (x : XHilbertSpace) : WeakDual ℝ XHilbertSpace :=
  StrongDual.toWeakDual (InnerProductSpace.toDual ℝ XHilbertSpace x)


/-- Every bounded sequence in the Hilbert model has a weakly convergent
subsequence.  This is sequential Banach--Alaoglu transported through the
Riesz representation theorem. -/
theorem weakSequentialCompactnessOnBounded_hilbert :
    WeakSequentialCompactnessOnBounded XHilbertSpace := by
  intro z C hz
  have hzmem (n : ℕ) : rieszWeakDual (z n) ∈
      WeakDual.toStrongDual ⁻¹' Metric.closedBall
        (0 : StrongDual ℝ XHilbertSpace) C := by
    change dist (InnerProductSpace.toDual ℝ XHilbertSpace (z n)) 0 ≤ C
    simpa [dist_zero_right] using hz n
  obtain ⟨w, hw, φ, hφ, hφWeakDual⟩ :=
    (WeakDual.isSeqCompact_closedBall ℝ XHilbertSpace
      (0 : StrongDual ℝ XHilbertSpace) C) hzmem
  let x : XHilbertSpace :=
    (InnerProductSpace.toDual ℝ XHilbertSpace).symm (WeakDual.toStrongDual w)
  refine ⟨x, φ, hφ, ?_⟩
  unfold WeaklyTendsto
  have hinj : Function.Injective (topDualPairing ℝ XHilbertSpace).flip := by
    intro u v huv
    apply (NormedSpace.inclusionInDoubleDualLi ℝ).injective
    ext g
    exact DFunLike.congr_fun huv g
  refine (WeakBilin.tendsto_iff_forall_eval_tendsto
    (B := (topDualPairing ℝ XHilbertSpace).flip) hinj).2 ?_
  intro g
  have heval :=
    (tendsto_iff_forall_eval_tendsto_topDualPairing.mp hφWeakDual)
      ((InnerProductSpace.toDual ℝ XHilbertSpace).symm g)
  convert heval using 1
  · ext i
    change g (z (φ i)) = inner ℝ (z (φ i))
      ((InnerProductSpace.toDual ℝ XHilbertSpace).symm g)
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  · congr 1
    change g x = w ((InnerProductSpace.toDual ℝ XHilbertSpace).symm g)
    rw [← WeakDual.toStrongDual_apply]
    change g ((InnerProductSpace.toDual ℝ XHilbertSpace).symm
      (WeakDual.toStrongDual w)) =
        WeakDual.toStrongDual w ((InnerProductSpace.toDual ℝ XHilbertSpace).symm g)
    rw [← InnerProductSpace.toDual_symm_apply]
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]

/-- Every bounded sequence in the paper's renormed space `XSpace` has a
weakly convergent subsequence. -/
theorem weakSequentialCompactnessOnBounded :
    WeakSequentialCompactnessOnBounded XSpace := by
  intro z C hz
  obtain ⟨x, φ, hφ, hweak⟩ :=
    weakSequentialCompactnessOnBounded_hilbert
      (fun n ↦ toHilbert (z n)) C
      (fun n ↦ (norm_toHilbert_le (z n)).trans (hz n))
  refine ⟨ofHilbert x, φ, hφ, ?_⟩
  have hm := hweak.map continuousLinearEquivHilbertSum.symm.toContinuousLinearMap
  simpa [Function.comp_def, continuousLinearEquivHilbertSum,
    linearEquivHilbertSum] using hm


end

end NormFormula.X
