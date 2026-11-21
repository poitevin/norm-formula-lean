import NormFormula.ContinuousLogic.LosAlong
import NormFormula.ContinuousLogic.FinitePatternTransfer
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Finite-pattern transfer along every free ultrafilter -/
namespace NormFormula.ContinuousLogic
noncomputable section
open Filter
open scoped Topology
universe u v w
attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.parameterPseudoMetricSpace MultiStructure.rowNonempty
  MultiStructure.parameterNonempty

def atTopApproximationScale (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    UltrafilterApproximationScale U where
  error n := 1/((n:ℝ)+1)
  error_pos n := by positivity
  tendsto_zero := tendsto_one_div_add_atTop_nhds_zero_nat.mono_left hU

namespace MultiFormula

theorem hasInfiniteIPWitness_reducedProductAlong_of_finitePatterns
    {Symbol : Type w} (M : MultiStructure.{u,v,w} Symbol) (bounds : M.Bounds)
    (φ : MultiFormula Symbol 1 1) (low high : ℝ)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (hp : HasFiniteIPPatternsInEveryDimension M φ low high) :
    HasInfiniteIPWitness (M.reducedProductAlong U bounds) φ low high := by
  classical
  choose r hr using fun n ↦ hp (n+1)
  let row (i n : ℕ) : M.Row :=
    if hi : i < n+1 then r n ⟨i,hi⟩ else Classical.choice M.rowNonempty
  refine ⟨fun i ↦ ReducedProductAlong.mk U bounds.row (row i), ?_⟩
  intro A B hAB
  let subset (n : ℕ) : Finset (Fin (n+1)) := Finset.univ.filter fun i ↦ i.val ∈ B
  choose p hhi hlo using fun n ↦ hr n (subset n)
  refine ⟨ReducedProductAlong.mk U bounds.parameter p, ?_, ?_⟩
  · intro i hi
    have hlos := realize_reducedProductAlong U (atTopApproximationScale U hU) M bounds φ
      (fun _ : Fin 1 ↦ row i) (fun _ : Fin 1 ↦ p)
    change (φ.realize _ _ _ : ℝ) ≤ low
    rw [hlos]
    apply ultralimitAlong_coe_le_of_eventually_le
    filter_upwards [hU (eventually_ge_atTop i)] with n hn
    have hin : i < n+1 := by omega
    have hiB : i ∉ B := Finset.disjoint_left.mp hAB hi
    have h := hlo n ⟨i,hin⟩ (by simp [subset,hiB])
    simpa [row, hin, hn, binaryValue] using h
  · intro i hi
    have hlos := realize_reducedProductAlong U (atTopApproximationScale U hU) M bounds φ
      (fun _ : Fin 1 ↦ row i) (fun _ : Fin 1 ↦ p)
    change high ≤ (φ.realize _ _ _ : ℝ)
    rw [hlos]
    apply le_ultralimitAlong_coe_of_eventually_le
    filter_upwards [hU (eventually_ge_atTop i)] with n hn
    have hin : i < n+1 := by omega
    have h := hhi n ⟨i,hin⟩ (by simp [subset,hi])
    simpa [row, hin, hn, binaryValue] using h

/-- The finite-box transfer lemma, with equality of the complete theory and
one infinite witness for every nonprincipal ultrafilter on `ℕ`. -/
theorem sameTheory_and_infiniteWitness_every_free_ultrafilter
    {Symbol : Type w} (M : MultiStructure.{u,v,w} Symbol) (bounds : M.Bounds)
    (φ : MultiFormula Symbol 1 1) (low high : ℝ)
    (hp : HasFiniteIPPatternsInEveryDimension M φ low high)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    MultiSameCompleteTheory M (M.reducedProductAlong U bounds) ∧
      HasInfiniteIPWitness (M.reducedProductAlong U bounds) φ low high :=
  ⟨multiSameCompleteTheory_reducedProductAlong U (atTopApproximationScale U hU) M bounds,
    hasInfiniteIPWitness_reducedProductAlong_of_finitePatterns M bounds φ low high U hU hp⟩
end MultiFormula
end
end NormFormula.ContinuousLogic
