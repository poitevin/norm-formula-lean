import NormFormula.Analytic.Separability
import NormFormula.Examples.HalfGraph
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Denumerable
import Mathlib.Topology.Bases

/-! # Identifying separable infinite-dimensional Hilbert carriers with `ℓ₂` -/
namespace NormFormula
noncomputable section
open TopologicalSpace Function
open scoped Topology

/-- An orthonormal family in a separable Hilbert space is countable. -/
theorem orthonormal_countable {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [SeparableSpace H] {v : ι → H}
    (hv : Orthonormal ℝ v) : Countable ι := by
  have hd : Pairwise (Disjoint on (fun i ↦ Metric.ball (v i) (1/3:ℝ))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hdist : dist (v i) (v j) < 2/3 := by
      have h := dist_triangle (v i) x (v j)
      rw [Metric.mem_ball, dist_comm x (v i)] at hx
      rw [Metric.mem_ball] at hy
      linarith
    have hs : ‖v i-v j‖^2 = 2 := by
      rw [norm_sub_sq_real, hv.norm_eq_one i, hv.norm_eq_one j, hv.inner_eq_zero hij]
      norm_num
    rw [dist_eq_norm] at hdist
    nlinarith [norm_nonneg (v i-v j)]
  exact hd.countable_of_isOpen_disjoint (fun _ ↦ Metric.isOpen_ball)
    (fun _ ↦ Metric.nonempty_ball.mpr (by norm_num))

/-- The standard real `ℓ₂` classification, with infinite dimension witnessed
by a countable linearly independent family. -/
theorem exists_hilbertEquivL2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SeparableSpace H] (v : ℕ → H) (hv : LinearIndependent ℝ v) :
    Nonempty (H ≃ₗᵢ[ℝ] HalfGraph.RealL2) := by
  classical
  obtain ⟨w,b,_⟩ := exists_hilbertBasis ℝ H
  letI : Countable w := orthonormal_countable b.orthonormal
  have hinf : Infinite w := by
    by_contra h
    haveI : Finite w := not_infinite_iff_finite.mp h
    letI := Fintype.ofFinite w
    letI : FiniteDimensional ℝ H := b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
    haveI : Finite ℕ := hv.finite
    exact not_finite ℕ
  letI : Infinite w := hinf
  let e : ℕ ≃ w := Classical.choice (inferInstance : Nonempty (ℕ ≃ w))
  let b' : HilbertBasis ℕ ℝ H := HilbertBasis.mk
    (b.orthonormal.comp e e.injective) (by
      have hr : Set.range (b ∘ e) = Set.range b := by
        ext x
        constructor
        · rintro ⟨n,rfl⟩; exact ⟨e n,rfl⟩
        · rintro ⟨i,rfl⟩; exact ⟨e.symm i, by simp⟩
      rw [hr]
      exact le_of_eq b.dense_span.symm)
  exact ⟨b'.repr⟩

/-- Scalar coordinate vectors form an infinite linearly independent family
in `ℓ₂`. -/
theorem l2_basis_linearIndependent : LinearIndependent ℝ HalfGraph.basisVector := by
  let f : HalfGraph.RealL2 →ₗ[ℝ] (ℕ → ℝ) :=
    { toFun := fun x ↦ x, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  exact LinearIndependent.of_comp f (Pi.linearIndependent_single_one ℕ ℝ)
end
end NormFormula
