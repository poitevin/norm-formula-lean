import NormFormula.ContinuousLogic.MultiLos
import NormFormula.ContinuousLogic.Compactness
import NormFormula.ContinuousLogic.FinitePatternTransfer

/-!
# Atomic finite-pattern compactness for many-predicate structures

Finite fixed-gap patterns for one named predicate are assembled into an
infinite witness in the many-predicate metric reduced product. Łoś's theorem
then supplies equality of every sentence value, including all other predicate
symbols in the ambient language.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Filter

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.parameterPseudoMetricSpace MultiStructure.rowNonempty
  MultiStructure.parameterNonempty

universe u v w

namespace MultiFormula

/-- In a bounded many-predicate structure, finite patterns for an atomic
predicate yield an infinite witness with the same fixed thresholds in a
same-theory metric reduced product. -/
theorem exists_sameTheory_atomic_infiniteWitness_of_finitePatterns
    {Symbol : Type w} (M : MultiStructure.{u, v, w} Symbol)
    (bounds : M.Bounds) (symbol : Symbol) (low high : ℝ)
    (hpatterns : HasFiniteIPPatternsInEveryDimension M
      (.predicate symbol 0 0) low high) :
    ∃ N : MultiStructure.{u, v, w} Symbol,
      MultiSameCompleteTheory M N ∧
      HasInfiniteIPWitness N (.predicate symbol 0 0) low high := by
  have hpatterns' : ∀ n : ℕ, ∃ rows : Fin (n + 1) → M.Row,
      NormFormula.IsIPPattern
        (fun i parameter =>
          (M.predicate symbol (rows i) parameter : ℝ)) low high := by
    intro n
    obtain ⟨rows, hrows⟩ := hpatterns (n + 1)
    exact ⟨rows, by
      simpa [MultiFormula.binaryValue, MultiFormula.realize] using hrows⟩
  choose finiteRows finitePattern using hpatterns'
  let defaultRow : M.Row := Classical.choice M.rowNonempty
  let rowRepresentative (i : ℕ) : ReducedSequence bounds.row := fun n =>
    if hi : i < n + 1 then finiteRows n ⟨i, hi⟩ else defaultRow
  let productRows : ℕ → (M.reducedProduct bounds).Row := fun i =>
    ReducedProduct.mk bounds.row (rowRepresentative i)
  refine ⟨M.reducedProduct bounds,
    multiSameCompleteTheory_reducedProduct M bounds, productRows, ?_⟩
  intro E F hdisjoint
  let highSubset (n : ℕ) : Finset (Fin (n + 1)) :=
    Finset.univ.filter fun i => (i : ℕ) ∈ F
  have hparameters : ∀ n : ℕ, ∃ parameter : M.Parameter,
      (∀ i ∈ highSubset n,
          high ≤ (M.predicate symbol (finiteRows n i) parameter : ℝ)) ∧
        (∀ i ∉ highSubset n,
          (M.predicate symbol (finiteRows n i) parameter : ℝ) ≤ low) :=
    fun n => finitePattern n (highSubset n)
  choose parameter parameterPattern using hparameters
  let parameterRepresentative : ReducedSequence bounds.parameter := parameter
  refine ⟨ReducedProduct.mk bounds.parameter parameterRepresentative, ?_, ?_⟩
  · intro i hiE
    change (multiReducedPredicate M bounds symbol
      (ReducedProduct.mk bounds.row (rowRepresentative i))
      (ReducedProduct.mk bounds.parameter parameterRepresentative) : ℝ) ≤ low
    rw [multiReducedPredicate_mk]
    apply ultralimit_coe_le_of_eventually_le
    filter_upwards [eventually_ge_indexUltrafilter i] with n hn
    have hin : i < n + 1 := Nat.lt_succ_of_le hn
    let index : Fin (n + 1) := ⟨i, hin⟩
    have hiNotF : i ∉ F := Finset.disjoint_left.mp hdisjoint hiE
    have hindex : index ∉ highSubset n := by
      simp [highSubset, index, hiNotF]
    have hlow := (parameterPattern n).2 index hindex
    simpa [rowRepresentative, parameterRepresentative, hn, hin, index] using hlow
  · intro i hiF
    change high ≤ (multiReducedPredicate M bounds symbol
      (ReducedProduct.mk bounds.row (rowRepresentative i))
      (ReducedProduct.mk bounds.parameter parameterRepresentative) : ℝ)
    rw [multiReducedPredicate_mk]
    apply le_ultralimit_coe_of_eventually_le
    filter_upwards [eventually_ge_indexUltrafilter i] with n hn
    have hin : i < n + 1 := Nat.lt_succ_of_le hn
    let index : Fin (n + 1) := ⟨i, hin⟩
    have hindex : index ∈ highSubset n := by
      simp [highSubset, index, hiF]
    have hhigh := (parameterPattern n).1 index hindex
    simpa [rowRepresentative, parameterRepresentative, hn, hin, index] using hhigh

/-- Atomic finite patterns therefore imply IP in the complete theory. -/
theorem atomic_hasIPInCompleteTheory_of_finitePatterns
    {Symbol : Type w} (M : MultiStructure.{u, v, w} Symbol)
    (bounds : M.Bounds) (symbol : Symbol) (low high : ℝ)
    (hgap : low < high)
    (hpatterns : HasFiniteIPPatternsInEveryDimension M
      (.predicate symbol 0 0) low high) :
    HasIPInCompleteTheory M (.predicate symbol 0 0) := by
  obtain ⟨N, hTheory, hWitness⟩ :=
    exists_sameTheory_atomic_infiniteWitness_of_finitePatterns
      M bounds symbol low high hpatterns
  exact ⟨N, hTheory, low, high, hgap, hWitness⟩

end MultiFormula

end

end NormFormula.ContinuousLogic
