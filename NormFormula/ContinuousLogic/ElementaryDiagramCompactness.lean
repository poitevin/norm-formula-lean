import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import NormFormula.ContinuousLogic.FiniteDiagramFamily
import NormFormula.ContinuousLogic.LosAlong

/-!
# Elementary-diagram compactness by a directed metric ultraproduct

The index set consists of a finite set of named diagram conditions and a
natural-number accuracy demand.  An ultrafilter extending its `atTop` filter
eventually contains every fixed condition and drives the errors to zero.
Finite approximate satisfiability supplies one global coordinate assignment
at each index.  The arbitrary-index Łoś theorem then turns all diagram
conditions into exact equalities.

The final generic theorem is stated in one ambient universe.  This includes
the paper's concrete languages and carrier sorts and keeps the directed
ultraproduct carriers in that same universe.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Filter
open scoped Topology

universe u

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.parameterPseudoMetricSpace MultiStructure.rowNonempty
  MultiStructure.parameterNonempty

/-- Directed indices: enlarge the finite condition set and increase the
accuracy counter. -/
abbrev ElementaryDiagramIndex {Symbol : Type u}
    (N : MultiStructure.{u, u, u} Symbol) :=
  Finset (NamedDiagramCondition N) × ℕ

/-- An ultrafilter extending the directed `atTop` filter of finite condition
sets and accuracy counters. -/
def elementaryDiagramUltrafilter {Symbol : Type u}
    (N : MultiStructure.{u, u, u} Symbol) :
    Ultrafilter (ElementaryDiagramIndex N) := by
  classical
  exact Ultrafilter.of atTop

/-- The diagram ultrafilter contains every `atTop`-eventual property. -/
theorem elementaryDiagramUltrafilter_le_atTop {Symbol : Type u}
    (N : MultiStructure.{u, u, u} Symbol) :
    (elementaryDiagramUltrafilter N : Filter (ElementaryDiagramIndex N)) ≤
      atTop := by
  classical
  exact Ultrafilter.of_le atTop

/-- Every fixed named condition occurs eventually in the directed index. -/
theorem eventually_condition_mem_elementaryDiagramUltrafilter
    {Symbol : Type u} {N : MultiStructure.{u, u, u} Symbol}
    (condition : NamedDiagramCondition N) :
    ∀ᶠ index : ElementaryDiagramIndex N in elementaryDiagramUltrafilter N,
      condition ∈ index.1 := by
  classical
  have htail : ∀ᶠ index : ElementaryDiagramIndex N in atTop,
      ({condition}, 0) ≤ index :=
    eventually_ge_atTop ({condition}, 0)
  filter_upwards [elementaryDiagramUltrafilter_le_atTop N htail] with index hindex
  exact hindex.1 (Finset.mem_singleton_self condition)

/-- Coordinate error `1/(n+1)`. -/
def elementaryDiagramError {Symbol : Type u}
    {N : MultiStructure.{u, u, u} Symbol}
    (index : ElementaryDiagramIndex N) : ℝ :=
  1 / ((index.2 : ℝ) + 1)

theorem elementaryDiagramError_pos {Symbol : Type u}
    {N : MultiStructure.{u, u, u} Symbol}
    (index : ElementaryDiagramIndex N) :
    0 < elementaryDiagramError index := by
  apply one_div_pos.mpr
  exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg index.2) zero_lt_one

/-- The coordinate errors tend to zero along the directed ultrafilter. -/
theorem tendsto_elementaryDiagramError_zero {Symbol : Type u}
    (N : MultiStructure.{u, u, u} Symbol) :
    Tendsto (elementaryDiagramError (N := N))
      (elementaryDiagramUltrafilter N) (𝓝 0) := by
  classical
  have hsnd : Tendsto
      (fun index : ElementaryDiagramIndex N ↦ index.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have herror : Tendsto (elementaryDiagramError (N := N)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hsnd
  exact herror.mono_left (elementaryDiagramUltrafilter_le_atTop N)

/-- The vanishing witness-error scale used in arbitrary-index Łoś. -/
def elementaryDiagramApproximationScale {Symbol : Type u}
    (N : MultiStructure.{u, u, u} Symbol) :
    UltrafilterApproximationScale (elementaryDiagramUltrafilter N) where
  error := elementaryDiagramError
  error_pos := elementaryDiagramError_pos
  tendsto_zero := tendsto_elementaryDiagramError_zero N

/-- In one ambient universe, bounded metric elementary-diagram compactness is
a theorem: finite approximate realizability produces the exact
formula-preserving reduct embedding. -/
theorem elementaryDiagramCompactness_of_bounds
    {Symbol Target : Type u} (f : Symbol → Target)
    (M : MultiStructure.{u, u, u} Target) (bounds : M.Bounds) :
    ElementaryDiagramCompactness f M := by
  intro N hfinite
  let U := elementaryDiagramUltrafilter N
  let scale := elementaryDiagramApproximationScale N
  have hcoordinate : ∀ index : ElementaryDiagramIndex N,
      Nonempty (FiniteNamedDiagramRealization f M N index.1
        (elementaryDiagramError index)) := by
    intro index
    exact exists_finiteNamedDiagramRealization f M N hfinite index.1
      (elementaryDiagramError index) (elementaryDiagramError_pos index)
  let coordinate (index : ElementaryDiagramIndex N) :
      FiniteNamedDiagramRealization f M N index.1
        (elementaryDiagramError index) :=
    Classical.choice (hcoordinate index)
  refine ⟨{
    expansion := M.reducedProductAlong U bounds
    sameTheory := multiSameCompleteTheory_reducedProductAlong U scale M bounds
    rowMap := fun x ↦ ReducedProductAlong.mk U bounds.row
      (fun index ↦ (coordinate index).rows x)
    parameterMap := fun y ↦ ReducedProductAlong.mk U bounds.parameter
      (fun index ↦ (coordinate index).parameters y)
    realize_reduct := ?_ }⟩
  intro rowVars parameterVars φ rowTuple parameterTuple
  let condition : NamedDiagramCondition N :=
    { rowVars := rowVars
      parameterVars := parameterVars
      formula := φ
      rows := rowTuple
      parameters := parameterTuple }
  let values : ElementaryDiagramIndex N → TruthValue := fun index ↦
    (φ.map f).realize M
      (fun i ↦ (coordinate index).rows (rowTuple i))
      (fun j ↦ (coordinate index).parameters (parameterTuple j))
  have hlos := MultiFormula.realize_reducedProductAlong U scale M bounds
    (φ.map f)
    (fun i index ↦ (coordinate index).rows (rowTuple i))
    (fun j index ↦ (coordinate index).parameters (parameterTuple j))
  have hdistEventually : ∀ᶠ index in U,
      dist (values index) (φ.realize N rowTuple parameterTuple) ≤
        elementaryDiagramError index := by
    have hmem := eventually_condition_mem_elementaryDiagramUltrafilter condition
    filter_upwards [hmem] with index hcondition
    have hrealize := (coordinate index).realizes condition hcondition
    simpa [values, condition, NamedDiagramCondition.target,
      Subtype.dist_eq] using hrealize.le
  have hvalues : Tendsto values U
      (𝓝 (φ.realize N rowTuple parameterTuple)) := by
    apply tendsto_iff_dist_tendsto_zero.2
    exact squeeze_zero'
      (Eventually.of_forall fun _ ↦ dist_nonneg)
      hdistEventually
      (tendsto_elementaryDiagramError_zero N)
  have hultralimit : ultralimitAlong U values =
      φ.realize N rowTuple parameterTuple :=
    ultralimitAlong_eq_of_tendsto hvalues
  exact hlos.trans (by simpa only [values] using hultralimit)

/-- NIP in a bounded expansion descends to its reduct. The elementary-diagram
construction discharges the embedding premise for arbitrary bounded structures. -/
theorem MultiFormula.nip_reduct_of_expansion_of_bounds
    {Symbol Target : Type u} (f : Symbol → Target)
    (M : MultiStructure.{u, u, u} Target) (bounds : M.Bounds)
    (φ : MultiFormula Symbol 1 1)
    (hNIP : MultiFormula.IsNIPInCompleteTheory M (φ.map f)) :
    MultiFormula.IsNIPInCompleteTheory (M.reduct f) φ :=
  MultiFormula.nip_reduct_of_expansion f M φ
    (hasSameTheoryReductEmbeddingProperty_of_elementaryDiagramCompactness f M
      (elementaryDiagramCompactness_of_bounds f M bounds)) hNIP

end

end NormFormula.ContinuousLogic
