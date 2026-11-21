import NormFormula.Analytic.XWeakCompactness
import NormFormula.Analytic.XYHilbertEquiv

/-!
# Separability of the constructed spaces

Finite-support vectors prove separability of the real ℓ₂ space underlying
`Y`. Product homeomorphisms and the established continuous linear
equivalences then transfer separability to `Y`, `XSpace`, their Hilbert
models, and the concrete direct sum `XYSpace`.
-/

namespace NormFormula

noncomputable section

open Filter TopologicalSpace
open scoped Topology ENNReal

/-- A homeomorphic image of a separable space is separable. -/
private theorem separableSpace_of_homeomorph
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [SeparableSpace A] (e : A ≃ₜ B) : SeparableSpace B := by
  have h : IsSeparable (Set.range e) := isSeparable_range e.continuous
  rw [e.surjective.range_eq] at h
  exact isSeparable_univ_iff.mp h

namespace HalfGraph

/-- Embed the first `k` real coordinates into `RealL2`. -/
def realL2HeadEmbed (k : ℕ) (v : Fin k → ℝ) : RealL2 :=
  ∑ i : Fin k, lp.single 2 (i : ℕ) (v i)

/-- The finite-head embedding into `RealL2` is continuous. -/
theorem continuous_realL2HeadEmbed (k : ℕ) :
    Continuous (realL2HeadEmbed k) := by
  apply continuous_finset_sum
  intro i hi
  exact (lp.isometry_single (E := fun _ : ℕ ↦ ℝ) (p := (2 : ENNReal))
    (i : ℕ)).continuous.comp (continuous_apply i)

/-- Restricting and re-embedding gives the standard finite head. -/
theorem realL2HeadEmbed_restrict (k : ℕ) (x : RealL2) :
    realL2HeadEmbed k (fun i ↦ x i) = lpHead (Finset.range k) x := by
  simp only [realL2HeadEmbed, lpHead, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.mp hi]

/-- The union of all finite-coordinate heads in `RealL2`. -/
def realL2FiniteHeadRange : Set RealL2 :=
  ⋃ k : ℕ, Set.range (realL2HeadEmbed k)

/-- Finite-coordinate vectors form a separable subset of `RealL2`. -/
theorem isSeparable_realL2FiniteHeadRange :
    IsSeparable realL2FiniteHeadRange := by
  exact IsSeparable.iUnion
    (fun k ↦ isSeparable_range (continuous_realL2HeadEmbed k))

/-- Finite-coordinate vectors are dense in `RealL2`. -/
theorem dense_realL2FiniteHeadRange :
    Dense realL2FiniteHeadRange := by
  rw [dense_iff_closure_eq]
  apply Set.Subset.antisymm
    (closure_minimal (Set.subset_univ _) isClosed_univ)
  intro x hx
  apply mem_closure_of_tendsto ((tendsto_lpHead x).comp tendsto_finset_range)
  filter_upwards with k
  refine Set.mem_iUnion.2 ⟨k, ?_⟩
  exact ⟨fun i ↦ x i, realL2HeadEmbed_restrict k x⟩

/-- The real square-summable sequence space is separable. -/
noncomputable instance : SeparableSpace RealL2 :=
  dense_realL2FiniteHeadRange.isSeparable_iff.mp
    isSeparable_realL2FiniteHeadRange

/-- The Hilbert product underlying `Y` is separable. -/
noncomputable instance : SeparableSpace HilbertSpace :=
  separableSpace_of_homeomorph
    (WithLp.homeomorphProd 2 RealL2 RealL2).symm

/-- The renormed space `Y` is separable. -/
noncomputable instance : SeparableSpace Y :=
  separableSpace_of_homeomorph
    Y.continuousLinearEquivHilbert.symm.toHomeomorph

end HalfGraph

namespace X

/-- The renormed dependent sum `XSpace` is separable. -/
noncomputable instance : SeparableSpace XSpace :=
  separableSpace_of_homeomorph
    continuousLinearEquivHilbertSum.symm.toHomeomorph

end X

namespace XY

/-- The Hilbert model of the direct sum is separable. -/
noncomputable instance : SeparableSpace XYHilbertSpace :=
  separableSpace_of_homeomorph
    (WithLp.homeomorphProd 2 X.XHilbertSpace HalfGraph.HilbertSpace).symm

/-- The concrete direct sum `X ⊕₂ Y` is separable. -/
noncomputable instance : SeparableSpace XYSpace :=
  separableSpace_of_homeomorph
    continuousLinearEquivHilbertSum.symm.toHomeomorph

end XY

end

end NormFormula
