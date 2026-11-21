import Mathlib.Data.Fintype.EquivFin
import NormFormula.ContinuousLogic.ElementaryDiagram

/-!
# Finite families of named elementary-diagram conditions

The earlier finite-fragment representation uses one common tuple.  For the
ultrafilter construction it is more convenient to start with arbitrary
constant instances and merge a finite family of them.  Variable reindexing
and finite deduplication of named elements perform that merge.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u v u' v' w z

attribute [local instance] MultiStructure.rowNonempty
  MultiStructure.parameterNonempty

namespace MultiFormula

/-- Add a new bound variable at index zero while reindexing the old free
variables through successors. -/
def liftReindex {n m : ℕ} (f : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cons 0 (fun i ↦ (f i).succ)

/-- Reindex the free variables of a formula. -/
def reindex {Symbol : Type w} {rowVars parameterVars rowVars' parameterVars' : ℕ}
    (rowMap : Fin rowVars → Fin rowVars')
    (parameterMap : Fin parameterVars → Fin parameterVars') :
    MultiFormula Symbol rowVars parameterVars →
      MultiFormula Symbol rowVars' parameterVars'
  | .predicate symbol i j => .predicate symbol (rowMap i) (parameterMap j)
  | .constant c => .constant c
  | .connective F formulas =>
      .connective F (fun i ↦ (formulas i).reindex rowMap parameterMap)
  | .iSupRow formula =>
      .iSupRow (formula.reindex (liftReindex rowMap) parameterMap)
  | .iInfRow formula =>
      .iInfRow (formula.reindex (liftReindex rowMap) parameterMap)
  | .iSupParameter formula =>
      .iSupParameter (formula.reindex rowMap (liftReindex parameterMap))
  | .iInfParameter formula =>
      .iInfParameter (formula.reindex rowMap (liftReindex parameterMap))

/-- Language maps commute with free-variable reindexing. -/
theorem map_reindex {Symbol : Type w} {Target : Type z}
    (f : Symbol → Target) :
    ∀ {rowVars parameterVars rowVars' parameterVars' : ℕ}
      (rowMap : Fin rowVars → Fin rowVars')
      (parameterMap : Fin parameterVars → Fin parameterVars')
      (φ : MultiFormula Symbol rowVars parameterVars),
      (φ.reindex rowMap parameterMap).map f =
        (φ.map f).reindex rowMap parameterMap := by
  intro rowVars parameterVars rowVars' parameterVars' rowMap parameterMap φ
  induction φ generalizing rowVars' parameterVars' with
  | predicate symbol i j => rfl
  | constant c => rfl
  | connective F formulas ih =>
      simp only [reindex, map]
      congr 1
      funext i
      exact ih i rowMap parameterMap
  | iSupRow formula ih =>
      simp only [reindex, map]
      congr 1
      exact ih (liftReindex rowMap) parameterMap
  | iInfRow formula ih =>
      simp only [reindex, map]
      congr 1
      exact ih (liftReindex rowMap) parameterMap
  | iSupParameter formula ih =>
      simp only [reindex, map]
      congr 1
      exact ih rowMap (liftReindex parameterMap)
  | iInfParameter formula ih =>
      simp only [reindex, map]
      congr 1
      exact ih rowMap (liftReindex parameterMap)

/-- Reindexing a formula is semantic precomposition of its assignments. -/
theorem realize_reindex {Symbol : Type w} :
    ∀ {rowVars parameterVars rowVars' parameterVars' : ℕ}
      (rowMap : Fin rowVars → Fin rowVars')
      (parameterMap : Fin parameterVars → Fin parameterVars')
      (φ : MultiFormula Symbol rowVars parameterVars)
      (M : MultiStructure.{u, v, w} Symbol)
      (rows : Fin rowVars' → M.Row)
      (parameters : Fin parameterVars' → M.Parameter),
      (φ.reindex rowMap parameterMap).realize M rows parameters =
        φ.realize M (fun i ↦ rows (rowMap i))
          (fun j ↦ parameters (parameterMap j)) := by
  intro rowVars parameterVars rowVars' parameterVars' rowMap parameterMap φ
  induction φ generalizing rowVars' parameterVars' with
  | predicate symbol i j =>
      intro M rows parameters
      rfl
  | constant c =>
      intro M rows parameters
      rfl
  | connective F formulas ih =>
      intro M rows parameters
      simp only [reindex, realize]
      congr 1
      funext i
      exact ih i rowMap parameterMap M rows parameters
  | iSupRow formula ih =>
      intro M rows parameters
      simp only [reindex, realize]
      apply iSup_congr
      intro x
      rw [ih (liftReindex rowMap) parameterMap M (Fin.cons x rows) parameters]
      congr 1
      funext i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j
        rfl
  | iInfRow formula ih =>
      intro M rows parameters
      simp only [reindex, realize]
      apply iInf_congr
      intro x
      rw [ih (liftReindex rowMap) parameterMap M (Fin.cons x rows) parameters]
      congr 1
      funext i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j
        rfl
  | iSupParameter formula ih =>
      intro M rows parameters
      simp only [reindex, realize]
      apply iSup_congr
      intro y
      rw [ih rowMap (liftReindex parameterMap) M rows (Fin.cons y parameters)]
      congr 1
      funext j
      refine Fin.cases ?_ ?_ j
      · rfl
      · intro k
        rfl
  | iInfParameter formula ih =>
      intro M rows parameters
      simp only [reindex, realize]
      apply iInf_congr
      intro y
      rw [ih rowMap (liftReindex parameterMap) M rows (Fin.cons y parameters)]
      congr 1
      funext j
      refine Fin.cases ?_ ?_ j
      · rfl
      · intro k
        rfl

end MultiFormula

/-- One formula with concrete named row and parameter tuples from `N`. -/
structure NamedDiagramCondition {Symbol : Type w}
    (N : MultiStructure.{u, v, w} Symbol) where
  rowVars : ℕ
  parameterVars : ℕ
  formula : MultiFormula Symbol rowVars parameterVars
  rows : Fin rowVars → N.Row
  parameters : Fin parameterVars → N.Parameter

namespace NamedDiagramCondition

variable {Symbol : Type w} {N : MultiStructure.{u, v, w} Symbol}

/-- The target value of a named condition in its home structure. -/
def target (condition : NamedDiagramCondition N) : TruthValue :=
  condition.formula.realize N condition.rows condition.parameters

end NamedDiagramCondition

/-- A finite indexed family of arbitrary named diagram conditions. -/
structure FiniteNamedDiagram {Symbol : Type w}
    (N : MultiStructure.{u, v, w} Symbol) where
  conditionCount : ℕ
  conditions : Fin conditionCount → NamedDiagramCondition N

namespace FiniteNamedDiagram

variable {Symbol : Type w} {N : MultiStructure.{u, v, w} Symbol}

/-- Regard a finite set of named conditions as a finite indexed family. -/
def ofFinset (conditions : Finset (NamedDiagramCondition N)) :
    FiniteNamedDiagram N where
  conditionCount := conditions.card
  conditions := fun i ↦ (conditions.equivFin.symm i).1

/-- All row elements named anywhere in the finite family. -/
def rowElements (diagram : FiniteNamedDiagram N) : Finset N.Row := by
  classical
  exact Finset.univ.biUnion fun i ↦
    Finset.univ.image (diagram.conditions i).rows

/-- All parameter elements named anywhere in the finite family. -/
def parameterElements (diagram : FiniteNamedDiagram N) : Finset N.Parameter := by
  classical
  exact Finset.univ.biUnion fun i ↦
    Finset.univ.image (diagram.conditions i).parameters

theorem condition_row_mem (diagram : FiniteNamedDiagram N)
    (i : Fin diagram.conditionCount)
    (j : Fin (diagram.conditions i).rowVars) :
    (diagram.conditions i).rows j ∈ diagram.rowElements := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

theorem condition_parameter_mem (diagram : FiniteNamedDiagram N)
    (i : Fin diagram.conditionCount)
    (j : Fin (diagram.conditions i).parameterVars) :
    (diagram.conditions i).parameters j ∈ diagram.parameterElements := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

/-- The unique common variable assigned to a named row element. -/
def rowIndex (diagram : FiniteNamedDiagram N)
    (i : Fin diagram.conditionCount)
    (j : Fin (diagram.conditions i).rowVars) :
    Fin diagram.rowElements.card :=
  diagram.rowElements.equivFin
    ⟨(diagram.conditions i).rows j, diagram.condition_row_mem i j⟩

/-- The unique common variable assigned to a named parameter element. -/
def parameterIndex (diagram : FiniteNamedDiagram N)
    (i : Fin diagram.conditionCount)
    (j : Fin (diagram.conditions i).parameterVars) :
    Fin diagram.parameterElements.card :=
  diagram.parameterElements.equivFin
    ⟨(diagram.conditions i).parameters j, diagram.condition_parameter_mem i j⟩

/-- The deduplicated common row tuple. -/
def rowTuple (diagram : FiniteNamedDiagram N) :
    Fin diagram.rowElements.card → N.Row :=
  fun k ↦ (diagram.rowElements.equivFin.symm k).1

/-- The deduplicated common parameter tuple. -/
def parameterTuple (diagram : FiniteNamedDiagram N) :
    Fin diagram.parameterElements.card → N.Parameter :=
  fun k ↦ (diagram.parameterElements.equivFin.symm k).1

@[simp]
theorem rowTuple_rowIndex (diagram : FiniteNamedDiagram N)
    (i : Fin diagram.conditionCount)
    (j : Fin (diagram.conditions i).rowVars) :
    diagram.rowTuple (diagram.rowIndex i j) = (diagram.conditions i).rows j := by
  simp [rowTuple, rowIndex]

@[simp]
theorem parameterTuple_parameterIndex (diagram : FiniteNamedDiagram N)
    (i : Fin diagram.conditionCount)
    (j : Fin (diagram.conditions i).parameterVars) :
    diagram.parameterTuple (diagram.parameterIndex i j) =
      (diagram.conditions i).parameters j := by
  simp [parameterTuple, parameterIndex]

/-- Merge a finite family of named conditions into one common-tuple finite
elementary-diagram fragment. -/
def toFragment (diagram : FiniteNamedDiagram N) :
    FiniteElementaryDiagramFragment N where
  rowVars := diagram.rowElements.card
  parameterVars := diagram.parameterElements.card
  conditionCount := diagram.conditionCount
  formulas := fun i ↦ (diagram.conditions i).formula.reindex
    (diagram.rowIndex i) (diagram.parameterIndex i)
  rows := diagram.rowTuple
  parameters := diagram.parameterTuple

@[simp]
theorem toFragment_target (diagram : FiniteNamedDiagram N)
    (i : Fin diagram.conditionCount) :
    diagram.toFragment.targets i = (diagram.conditions i).target := by
  rw [NamedDiagramCondition.target, FiniteElementaryDiagramFragment.targets]
  change ((diagram.conditions i).formula.reindex
      (diagram.rowIndex i) (diagram.parameterIndex i)).realize N
        diagram.rowTuple diagram.parameterTuple = _
  rw [MultiFormula.realize_reindex]
  congr 1
  · funext j
    exact diagram.rowTuple_rowIndex i j
  · funext j
    exact diagram.parameterTuple_parameterIndex i j

/-- Extend a realization of the deduplicated finite row tuple to a total map
on all named row elements. -/
def extendRows {Row : Type u'}
    (diagram : FiniteNamedDiagram N)
    (tuple : Fin diagram.rowElements.card → Row)
    (default : Row) : N.Row → Row := by
  classical
  intro x
  exact if hx : x ∈ diagram.rowElements then
    tuple (diagram.rowElements.equivFin ⟨x, hx⟩) else default

/-- Extend a realization of the deduplicated finite parameter tuple to a
total map. -/
def extendParameters {Parameter : Type v'}
    (diagram : FiniteNamedDiagram N)
    (tuple : Fin diagram.parameterElements.card → Parameter)
    (default : Parameter) : N.Parameter → Parameter := by
  classical
  intro y
  exact if hy : y ∈ diagram.parameterElements then
    tuple (diagram.parameterElements.equivFin ⟨y, hy⟩) else default

@[simp]
theorem extendRows_condition {Row : Type u'}
    (diagram : FiniteNamedDiagram N)
    (tuple : Fin diagram.rowElements.card → Row) (default : Row)
    (i : Fin diagram.conditionCount)
    (j : Fin (diagram.conditions i).rowVars) :
    diagram.extendRows tuple default ((diagram.conditions i).rows j) =
      tuple (diagram.rowIndex i j) := by
  simp [extendRows, rowIndex, diagram.condition_row_mem i j]

@[simp]
theorem extendParameters_condition {Parameter : Type v'}
    (diagram : FiniteNamedDiagram N)
    (tuple : Fin diagram.parameterElements.card → Parameter)
    (default : Parameter) (i : Fin diagram.conditionCount)
    (j : Fin (diagram.conditions i).parameterVars) :
    diagram.extendParameters tuple default
        ((diagram.conditions i).parameters j) =
      tuple (diagram.parameterIndex i j) := by
  simp [extendParameters, parameterIndex,
    diagram.condition_parameter_mem i j]

/-- Evaluation of a merged, reindexed condition is evaluation of the
original condition under the extended global maps. -/
theorem mapped_toFragment_realize
    {Target : Type z} (f : Symbol → Target)
    (M : MultiStructure.{u', v', z} Target)
    (diagram : FiniteNamedDiagram N)
    (rowTuple : Fin diagram.rowElements.card → M.Row)
    (parameterTuple : Fin diagram.parameterElements.card → M.Parameter)
    (defaultRow : M.Row) (defaultParameter : M.Parameter)
    (i : Fin diagram.conditionCount) :
    ((diagram.toFragment.formulas i).map f).realize M
        rowTuple parameterTuple =
      ((diagram.conditions i).formula.map f).realize M
        (fun j ↦ diagram.extendRows rowTuple defaultRow
          ((diagram.conditions i).rows j))
        (fun j ↦ diagram.extendParameters parameterTuple defaultParameter
          ((diagram.conditions i).parameters j)) := by
  change ((((diagram.conditions i).formula.reindex
      (diagram.rowIndex i) (diagram.parameterIndex i)).map f).realize M
        rowTuple parameterTuple) = _
  rw [MultiFormula.map_reindex, MultiFormula.realize_reindex]
  congr 1
  · funext j
    symm
    exact diagram.extendRows_condition rowTuple defaultRow i j
  · funext j
    symm
    exact diagram.extendParameters_condition parameterTuple defaultParameter i j

end FiniteNamedDiagram

/-- Global row and parameter maps approximately realizing a finite set of
named conditions. -/
structure FiniteNamedDiagramRealization
    {Symbol : Type w} {Target : Type z}
    (f : Symbol → Target) (M : MultiStructure.{u', v', z} Target)
    (N : MultiStructure.{u, v, w} Symbol)
    (conditions : Finset (NamedDiagramCondition N)) (ε : ℝ) where
  rows : N.Row → M.Row
  parameters : N.Parameter → M.Parameter
  realizes : ∀ condition ∈ conditions,
    dist (((condition.formula.map f).realize M
        (fun i ↦ rows (condition.rows i))
        (fun j ↦ parameters (condition.parameters j)) :
          TruthValue) : ℝ) ((condition.target : TruthValue) : ℝ) < ε

/-- The common-tuple finite-fragment hypothesis realizes every finite set of
arbitrary named conditions by total maps. -/
theorem exists_finiteNamedDiagramRealization
    {Symbol : Type w} {Target : Type z}
    (f : Symbol → Target) (M : MultiStructure.{u', v', z} Target)
    (N : MultiStructure.{u, v, w} Symbol)
    (hfinite : ∀ (fragment : FiniteElementaryDiagramFragment N) (ε : ℝ),
      0 < ε →
        ∃ rows : Fin fragment.rowVars → M.Row,
          ∃ parameters : Fin fragment.parameterVars → M.Parameter,
            ∀ i : Fin fragment.conditionCount,
              |((((fragment.formulas i).map f).realize M rows parameters :
                  TruthValue) : ℝ) -
                ((fragment.targets i : TruthValue) : ℝ)| < ε)
    (conditions : Finset (NamedDiagramCondition N)) (ε : ℝ) (hε : 0 < ε) :
    Nonempty (FiniteNamedDiagramRealization f M N conditions ε) := by
  let diagram := FiniteNamedDiagram.ofFinset conditions
  obtain ⟨rowTuple, parameterTuple, hrealize⟩ :=
    hfinite diagram.toFragment ε hε
  let defaultRow : M.Row := Classical.choice M.rowNonempty
  let defaultParameter : M.Parameter := Classical.choice M.parameterNonempty
  refine ⟨{
    rows := diagram.extendRows rowTuple defaultRow
    parameters := diagram.extendParameters parameterTuple defaultParameter
    realizes := ?_ }⟩
  intro condition hcondition
  let i : Fin diagram.conditionCount :=
    conditions.equivFin ⟨condition, hcondition⟩
  have hi : diagram.conditions i = condition := by
    change (conditions.equivFin.symm i).1 = condition
    simpa only [i] using congrArg Subtype.val
      (conditions.equivFin.symm_apply_apply ⟨condition, hcondition⟩)
  have hmerged := diagram.mapped_toFragment_realize f M rowTuple
    parameterTuple defaultRow defaultParameter i
  have htarget := diagram.toFragment_target i
  have h := hrealize i
  rw [hmerged, htarget] at h
  have hall :
      dist (((diagram.conditions i).formula.map f).realize M
          (fun j ↦ diagram.extendRows rowTuple defaultRow
            ((diagram.conditions i).rows j))
          (fun j ↦ diagram.extendParameters parameterTuple defaultParameter
            ((diagram.conditions i).parameters j)) : ℝ)
        ((diagram.conditions i).target : ℝ) < ε := by
    simpa only [Real.dist_eq] using h
  exact hi ▸ hall

end

end NormFormula.ContinuousLogic
