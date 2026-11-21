import NormFormula.ContinuousLogic.ElementaryDiagram
import NormFormula.ContinuousLogic.MultiLos

/-!
# Sequential realization of an elementary diagram

This file connects elementary-diagram compactness to the concrete
many-predicate reduced product.  A simultaneous sequence of approximate
realizations of every constant instance gives an exact formula-preserving map
into the metric reduced product by Łoś's theorem.

For an arbitrary (possibly uncountable) diagram, producing such one sequence
is a genuine diagonalization assumption.  The general compactness theorem
will instead require an ultraproduct indexed by finite diagram fragments.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Filter
open scoped Topology

universe u v w z

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.parameterPseudoMetricSpace MultiStructure.rowNonempty
  MultiStructure.parameterNonempty

/-- One simultaneous sequence of approximate realizations of the complete
constant-enriched reduct diagram.  Convergence is stated along the fixed
nonprincipal ultrafilter used by the metric reduced product. -/
structure SequentialReductApproximation
    {Symbol : Type w} {Target : Type z}
    (f : Symbol → Target) (M : MultiStructure.{u, v, z} Target)
    (N : MultiStructure.{u, v, w} Symbol) where
  rows : ℕ → N.Row → M.Row
  parameters : ℕ → N.Parameter → M.Parameter
  realize_tendsto : ∀ {rowVars parameterVars : ℕ}
    (φ : MultiFormula Symbol rowVars parameterVars)
    (rowTuple : Fin rowVars → N.Row)
    (parameterTuple : Fin parameterVars → N.Parameter),
    Tendsto
      (fun n ↦ (φ.map f).realize M
        (fun i ↦ rows n (rowTuple i))
        (fun j ↦ parameters n (parameterTuple j)))
      indexUltrafilter
      (𝓝 (φ.realize N rowTuple parameterTuple))

/-- A simultaneous sequential diagram approximation becomes an exact reduct
embedding into the many-predicate metric reduced product. -/
theorem sameTheoryReductEmbedding_of_sequentialApproximation
    {Symbol : Type w} {Target : Type z}
    (f : Symbol → Target) (M : MultiStructure.{u, v, z} Target)
    (bounds : M.Bounds) (N : MultiStructure.{u, v, w} Symbol)
    (approximation : SequentialReductApproximation f M N) :
    Nonempty (MultiStructure.SameTheoryReductEmbedding f M N) := by
  refine ⟨{
    expansion := M.reducedProduct bounds
    sameTheory := multiSameCompleteTheory_reducedProduct M bounds
    rowMap := fun x ↦ ReducedProduct.mk bounds.row
      (fun n ↦ approximation.rows n x)
    parameterMap := fun y ↦ ReducedProduct.mk bounds.parameter
      (fun n ↦ approximation.parameters n y)
    realize_reduct := ?_ }⟩
  intro rowVars parameterVars φ rowTuple parameterTuple
  let values : ℕ → TruthValue := fun n ↦ (φ.map f).realize M
    (fun i ↦ approximation.rows n (rowTuple i))
    (fun j ↦ approximation.parameters n (parameterTuple j))
  have hlos := MultiFormula.realize_reducedProduct M bounds (φ.map f)
    (fun i n ↦ approximation.rows n (rowTuple i))
    (fun j n ↦ approximation.parameters n (parameterTuple j))
  have hultralimit : Tendsto values indexUltrafilter
      (𝓝 (ultralimit values)) :=
    tendsto_ultralimit values
  have htarget : Tendsto values indexUltrafilter
      (𝓝 (φ.realize N rowTuple parameterTuple)) := by
    simpa only [values] using
      approximation.realize_tendsto φ rowTuple parameterTuple
  have heq : ultralimit values = φ.realize N rowTuple parameterTuple :=
    tendsto_nhds_unique hultralimit htarget
  exact hlos.trans (by simpa only [values] using heq)

/-- A sequential version of elementary-diagram compactness: finite
approximate satisfiability can be diagonalized into one simultaneous
ultrafilter-convergent sequence. -/
def SequentialElementaryDiagramCompactness
    {Symbol : Type w} {Target : Type z}
    (f : Symbol → Target) (M : MultiStructure.{u, v, z} Target) : Prop :=
  ∀ N : MultiStructure.{u, v, w} Symbol,
    (∀ (fragment : FiniteElementaryDiagramFragment N) (ε : ℝ), 0 < ε →
      ∃ rows : Fin fragment.rowVars → M.Row,
        ∃ parameters : Fin fragment.parameterVars → M.Parameter,
          ∀ i : Fin fragment.conditionCount,
            |((((fragment.formulas i).map f).realize M rows parameters :
                TruthValue) : ℝ) -
              ((fragment.targets i : TruthValue) : ℝ)| < ε) →
      Nonempty (SequentialReductApproximation f M N)

/-- Sequential elementary-diagram compactness implies the exact compactness
interface, via the many-predicate reduced product and Łoś's theorem. -/
theorem elementaryDiagramCompactness_of_sequential
    {Symbol : Type w} {Target : Type z}
    (f : Symbol → Target) (M : MultiStructure.{u, v, z} Target)
    (bounds : M.Bounds)
    (hsequential : SequentialElementaryDiagramCompactness f M) :
    ElementaryDiagramCompactness f M := by
  intro N hfinite
  obtain ⟨approximation⟩ := hsequential N hfinite
  exact sameTheoryReductEmbedding_of_sequentialApproximation
    f M bounds N approximation

end

end NormFormula.ContinuousLogic
