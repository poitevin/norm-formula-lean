import NormFormula.ContinuousLogic.Los

/-!
# Finite atomic patterns give an infinite ultrapower witness

This file completes the atomic compactness implication used by the norm
formula.  A finite pattern of dimension `n + 1` is placed in coordinate `n`.
Each eventual row and each parameter for a pair of finite disjoint sets is
then represented by a coordinate sequence.  Once the coordinate dimension
contains all relevant indices, the desired inequalities hold on a tail and
therefore pass to the ultralimit.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Filter

attribute [local instance] Structure.rowPseudoMetricSpace
  Structure.parameterPseudoMetricSpace Structure.rowNonempty
  Structure.parameterNonempty

universe u v

/-- A bounded two-sorted structure satisfies the atomic finite-pattern
compactness principle, witnessed by its metric ultrapower. -/
theorem atomicFinitePatternCompactness_of_bounds
    (M : Structure.{u, v}) (bounds : M.Bounds) :
    AtomicFinitePatternCompactness M := by
  intro low high hgap hpatterns
  have hpatterns' : ∀ n : ℕ, ∃ rows : Fin (n + 1) → M.Row,
      NormFormula.IsIPPattern
        (fun i y ↦ Formula.atomic.binaryValue M (rows i) y) low high :=
    fun n ↦ hpatterns (n + 1)
  choose finiteRows finitePattern using hpatterns'
  let defaultRow : M.Row := Classical.choice M.rowNonempty
  let rowRepresentative (i : ℕ) : ReducedSequence bounds.row := fun n ↦
    if hi : i < n + 1 then finiteRows n ⟨i, hi⟩ else defaultRow
  let productRows : ℕ → (M.reducedProduct bounds).Row := fun i ↦
    ReducedProduct.mk bounds.row (rowRepresentative i)
  refine ⟨M.reducedProduct bounds, sameCompleteTheory_reducedProduct M bounds,
    low, high, hgap, productRows, ?_⟩
  intro E F hdisjoint
  let highSubset (n : ℕ) : Finset (Fin (n + 1)) :=
    Finset.univ.filter fun i ↦ (i : ℕ) ∈ F
  have hparameters : ∀ n : ℕ, ∃ parameter : M.Parameter,
      (∀ i ∈ highSubset n,
          high ≤ Formula.atomic.binaryValue M (finiteRows n i) parameter) ∧
        (∀ i ∉ highSubset n,
          Formula.atomic.binaryValue M (finiteRows n i) parameter ≤ low) :=
    fun n ↦ finitePattern n (highSubset n)
  choose parameter parameterPattern using hparameters
  let parameterRepresentative : ReducedSequence bounds.parameter := parameter
  refine ⟨ReducedProduct.mk bounds.parameter parameterRepresentative, ?_, ?_⟩
  · intro i hiE
    change (reducedPredicate M bounds
      (ReducedProduct.mk bounds.row (rowRepresentative i))
      (ReducedProduct.mk bounds.parameter parameterRepresentative) : ℝ) ≤ low
    rw [reducedPredicate_mk]
    apply ultralimit_coe_le_of_eventually_le
    filter_upwards [eventually_ge_indexUltrafilter i] with n hn
    have hin : i < n + 1 := Nat.lt_succ_of_le hn
    let index : Fin (n + 1) := ⟨i, hin⟩
    have hiNotF : i ∉ F := Finset.disjoint_left.mp hdisjoint hiE
    have hindex : index ∉ highSubset n := by
      simp [highSubset, index, hiNotF]
    have hlow := (parameterPattern n).2 index hindex
    simpa [Formula.atomic_binaryValue, rowRepresentative,
      parameterRepresentative, hn, hin, index] using hlow
  · intro i hiF
    change high ≤ (reducedPredicate M bounds
      (ReducedProduct.mk bounds.row (rowRepresentative i))
      (ReducedProduct.mk bounds.parameter parameterRepresentative) : ℝ)
    rw [reducedPredicate_mk]
    apply le_ultralimit_coe_of_eventually_le
    filter_upwards [eventually_ge_indexUltrafilter i] with n hn
    have hin : i < n + 1 := Nat.lt_succ_of_le hn
    let index : Fin (n + 1) := ⟨i, hin⟩
    have hindex : index ∈ highSubset n := by
      simp [highSubset, index, hiF]
    have hhigh := (parameterPattern n).1 index hindex
    simpa [Formula.atomic_binaryValue, rowRepresentative,
      parameterRepresentative, hn, hin, index] using hhigh

end

end NormFormula.ContinuousLogic
