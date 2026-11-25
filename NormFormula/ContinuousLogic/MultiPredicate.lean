import NormFormula.ContinuousLogic.Basic

/-!
# A many-predicate bounded continuous language

The first compactness vertical slice used one distinguished binary predicate.
For expansions and reducts we need a predicate alphabet.  This file provides
the corresponding two-sorted formula syntax, structures, evaluation, language
maps, and the fundamental theorem that evaluation is preserved when a formula
is mapped into a larger language and the structure is reduced along the same
map.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open scoped Topology

universe u v u' v' w w'

/-- Formulae in a two-sorted bounded language with a type `Symbol` of binary
predicate symbols. -/
inductive MultiFormula (Symbol : Type w) : ℕ → ℕ → Type w
  | predicate {rowVars parameterVars : ℕ} :
      Symbol → Fin rowVars → Fin parameterVars →
        MultiFormula Symbol rowVars parameterVars
  | constant {rowVars parameterVars : ℕ} :
      TruthValue → MultiFormula Symbol rowVars parameterVars
  | connective {rowVars parameterVars arity : ℕ} :
      Connective arity →
      (Fin arity → MultiFormula Symbol rowVars parameterVars) →
      MultiFormula Symbol rowVars parameterVars
  | iSupRow {rowVars parameterVars : ℕ} :
      MultiFormula Symbol (rowVars + 1) parameterVars →
      MultiFormula Symbol rowVars parameterVars
  | iInfRow {rowVars parameterVars : ℕ} :
      MultiFormula Symbol (rowVars + 1) parameterVars →
      MultiFormula Symbol rowVars parameterVars
  | iSupParameter {rowVars parameterVars : ℕ} :
      MultiFormula Symbol rowVars (parameterVars + 1) →
      MultiFormula Symbol rowVars parameterVars
  | iInfParameter {rowVars parameterVars : ℕ} :
      MultiFormula Symbol rowVars (parameterVars + 1) →
      MultiFormula Symbol rowVars parameterVars

/-- A bounded two-sorted structure for a many-predicate language. -/
structure MultiStructure (Symbol : Type w) where
  Row : Type u
  Parameter : Type v
  [rowPseudoMetricSpace : PseudoMetricSpace Row]
  [parameterPseudoMetricSpace : PseudoMetricSpace Parameter]
  [rowNonempty : Nonempty Row]
  [parameterNonempty : Nonempty Parameter]
  predicate : Symbol → Row → Parameter → TruthValue
  predicate_uniformContinuous : ∀ symbol,
    UniformContinuous fun p : Row × Parameter ↦ predicate symbol p.1 p.2

namespace MultiFormula

/-- Map every predicate symbol of a formula along a language map. -/
def map {Symbol : Type w} {Target : Type w'}
    (f : Symbol → Target) {rowVars parameterVars : ℕ} :
    MultiFormula Symbol rowVars parameterVars →
      MultiFormula Target rowVars parameterVars
  | .predicate symbol i j => .predicate (f symbol) i j
  | .constant c => .constant c
  | .connective F formulas => .connective F (fun i ↦ (formulas i).map f)
  | .iSupRow formula => .iSupRow (formula.map f)
  | .iInfRow formula => .iInfRow (formula.map f)
  | .iSupParameter formula => .iSupParameter (formula.map f)
  | .iInfParameter formula => .iInfParameter (formula.map f)

/-- Mapping every predicate symbol by the identity changes no formula. -/
@[simp]
theorem map_id {Symbol : Type w} {rowVars parameterVars : ℕ}
    (formula : MultiFormula Symbol rowVars parameterVars) :
    formula.map id = formula := by
  induction formula with
  | predicate symbol i j => rfl
  | constant c => rfl
  | connective F formulas ih =>
      simp only [map]
      congr 1
      funext i
      exact ih i
  | iSupRow formula ih => simp only [map, ih]
  | iInfRow formula ih => simp only [map, ih]
  | iSupParameter formula ih => simp only [map, ih]
  | iInfParameter formula ih => simp only [map, ih]

/-- Semantic evaluation in a many-predicate bounded structure. -/
def realize {Symbol : Type w} {rowVars parameterVars : ℕ}
    (φ : MultiFormula Symbol rowVars parameterVars)
    (M : MultiStructure Symbol)
    (rows : Fin rowVars → M.Row)
    (parameters : Fin parameterVars → M.Parameter) : TruthValue :=
  match φ with
  | .predicate symbol i j => M.predicate symbol (rows i) (parameters j)
  | .constant c => c
  | .connective F formulas =>
      F fun i ↦ (formulas i).realize M rows parameters
  | .iSupRow formula =>
      ⨆ x : M.Row, formula.realize M (Fin.cons x rows) parameters
  | .iInfRow formula =>
      ⨅ x : M.Row, formula.realize M (Fin.cons x rows) parameters
  | .iSupParameter formula =>
      ⨆ y : M.Parameter, formula.realize M rows (Fin.cons y parameters)
  | .iInfParameter formula =>
      ⨅ y : M.Parameter, formula.realize M rows (Fin.cons y parameters)

/-- Real-valued evaluation of a formula with one free variable of each sort. -/
def binaryValue {Symbol : Type w} (φ : MultiFormula Symbol 1 1)
    (M : MultiStructure Symbol) : M.Row → M.Parameter → ℝ :=
  fun x y ↦ (φ.realize M (fun _ ↦ x) (fun _ ↦ y) : ℝ)

end MultiFormula

/-- A sentence in a many-predicate language has no free variables. -/
abbrev MultiSentence (Symbol : Type w) := MultiFormula Symbol 0 0

namespace MultiSentence

/-- The truth value of a many-predicate sentence in a structure. -/
def value {Symbol : Type w} (φ : MultiSentence Symbol)
    (M : MultiStructure Symbol) : TruthValue :=
  φ.realize M Fin.elim0 Fin.elim0

end MultiSentence

/-- Two many-predicate structures have the same complete theory when every
sentence has the same truth value. -/
def MultiSameCompleteTheory {Symbol : Type w}
    (M : MultiStructure.{u, v, w} Symbol)
    (N : MultiStructure.{u', v', w} Symbol) : Prop :=
  ∀ φ : MultiSentence Symbol, φ.value M = φ.value N

namespace MultiSameCompleteTheory


end MultiSameCompleteTheory

namespace MultiFormula

/-- Two formulae are equivalent in the complete theory of `M` when they have
the same realization under every assignment in every same-theory structure
of the ambient carrier universes. -/
def EquivalentInCompleteTheory {Symbol : Type w}
    (M : MultiStructure.{u, v, w} Symbol)
    {rowVars parameterVars : ℕ}
    (φ ψ : MultiFormula Symbol rowVars parameterVars) : Prop :=
  ∀ (N : MultiStructure.{u, v, w} Symbol),
    MultiSameCompleteTheory M N →
    ∀ (rows : Fin rowVars → N.Row)
      (parameters : Fin parameterVars → N.Parameter),
      φ.realize N rows parameters = ψ.realize N rows parameters

end MultiFormula

namespace MultiStructure

/-- Reduce a structure along a map from a smaller predicate alphabet into a
larger one. -/
def reduct {Symbol : Type w} {Target : Type w'}
    (f : Symbol → Target) (M : MultiStructure Target) :
    MultiStructure Symbol where
  Row := M.Row
  Parameter := M.Parameter
  rowPseudoMetricSpace := M.rowPseudoMetricSpace
  parameterPseudoMetricSpace := M.parameterPseudoMetricSpace
  rowNonempty := M.rowNonempty
  parameterNonempty := M.parameterNonempty
  predicate := fun symbol ↦ M.predicate (f symbol)
  predicate_uniformContinuous := fun symbol ↦
    M.predicate_uniformContinuous (f symbol)

end MultiStructure

namespace MultiFormula

/-- Mapping a formula and interpreting it in the larger structure agrees with
interpreting the original formula in the reduct.  This includes all four
quantifier constructors. -/
theorem realize_map_reduct
    {Symbol : Type w} {Target : Type w'}
    (f : Symbol → Target) (M : MultiStructure Target)
    {rowVars parameterVars : ℕ}
    (φ : MultiFormula Symbol rowVars parameterVars) :
    ∀ (rows : Fin rowVars → M.Row)
      (parameters : Fin parameterVars → M.Parameter),
      (φ.map f).realize M rows parameters =
        φ.realize (M.reduct f) rows parameters := by
  induction φ with
  | predicate symbol i j =>
      intro rows parameters
      rfl
  | constant c =>
      intro rows parameters
      rfl
  | connective F formulas ih =>
      intro rows parameters
      simp only [map, realize]
      congr 1
      funext i
      exact ih i rows parameters
  | iSupRow formula ih =>
      intro rows parameters
      simp only [map, realize]
      exact iSup_congr fun x ↦ ih (Fin.cons x rows) parameters
  | iInfRow formula ih =>
      intro rows parameters
      simp only [map, realize]
      exact iInf_congr fun x ↦ ih (Fin.cons x rows) parameters
  | iSupParameter formula ih =>
      intro rows parameters
      simp only [map, realize]
      exact iSup_congr fun y ↦ ih rows (Fin.cons y parameters)
  | iInfParameter formula ih =>
      intro rows parameters
      simp only [map, realize]
      exact iInf_congr fun y ↦ ih rows (Fin.cons y parameters)


end MultiFormula

namespace MultiSameCompleteTheory


end MultiSameCompleteTheory

end


end NormFormula.ContinuousLogic
