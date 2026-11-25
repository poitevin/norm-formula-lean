import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Order.CompleteLatticeIntervals
import NormFormula.ModelTheory.ContinuousIP

/-!
# A minimal bounded continuous-logic fragment

This file begins the continuous-model-theory layer needed by the paper.  The
language has two sorts and one `[0,1]`-valued binary predicate, arbitrary
continuous connectives, and infimum/supremum quantifiers over either sort.
It is intentionally small, but its notions of formula evaluation, complete
theory, and theory-level IP are semantic rather than placeholders.

The one theorem not yet available in Mathlib is isolated as
`FinitePatternCompactness`: finite fixed-gap patterns in a distinguished
model yield an infinite IP witness in a model with the same complete theory.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open scoped Topology

universe u v u' v'

/-- The truth-value interval for the bounded fragment. -/
abbrev TruthValue := Set.Icc (0 : ℝ) 1

/-- The least bounded truth value. -/
def zeroTruthValue : TruthValue := ⟨0, by constructor <;> norm_num⟩

@[simp]
theorem zeroTruthValue_coe : (zeroTruthValue : ℝ) = 0 :=
  rfl

/-- A finitary continuous connective on bounded truth values. -/
structure Connective (arity : ℕ) where
  toFun : (Fin arity → TruthValue) → TruthValue
  continuous_toFun : Continuous toFun

instance {arity : ℕ} : CoeFun (Connective arity)
    (fun _ ↦ (Fin arity → TruthValue) → TruthValue) :=
  ⟨Connective.toFun⟩

/-- Formulae in the two-sorted language.  `rowVars` and `parameterVars` count
the free variables of the two sorts.  A newly quantified variable is placed
at index zero. -/
inductive Formula : ℕ → ℕ → Type
  | predicate {rowVars parameterVars : ℕ} :
      Fin rowVars → Fin parameterVars → Formula rowVars parameterVars
  | constant {rowVars parameterVars : ℕ} :
      TruthValue → Formula rowVars parameterVars
  | connective {rowVars parameterVars arity : ℕ} :
      Connective arity →
      (Fin arity → Formula rowVars parameterVars) →
      Formula rowVars parameterVars
  | iSupRow {rowVars parameterVars : ℕ} :
      Formula (rowVars + 1) parameterVars → Formula rowVars parameterVars
  | iInfRow {rowVars parameterVars : ℕ} :
      Formula (rowVars + 1) parameterVars → Formula rowVars parameterVars
  | iSupParameter {rowVars parameterVars : ℕ} :
      Formula rowVars (parameterVars + 1) → Formula rowVars parameterVars
  | iInfParameter {rowVars parameterVars : ℕ} :
      Formula rowVars (parameterVars + 1) → Formula rowVars parameterVars

/-- A bounded two-sorted structure for the language's distinguished binary
predicate.  Uniform continuity is part of the structure, as in continuous
logic. -/
structure Structure where
  Row : Type u
  Parameter : Type v
  [rowPseudoMetricSpace : PseudoMetricSpace Row]
  [parameterPseudoMetricSpace : PseudoMetricSpace Parameter]
  [rowNonempty : Nonempty Row]
  [parameterNonempty : Nonempty Parameter]
  predicate : Row → Parameter → TruthValue
  predicate_uniformContinuous :
    UniformContinuous fun p : Row × Parameter ↦ predicate p.1 p.2

namespace Formula

/-- Semantic evaluation of a formula in a bounded structure. -/
def realize {rowVars parameterVars : ℕ}
    (φ : Formula rowVars parameterVars) (M : Structure)
    (rows : Fin rowVars → M.Row)
    (parameters : Fin parameterVars → M.Parameter) : TruthValue :=
  match φ with
  | .predicate i j => M.predicate (rows i) (parameters j)
  | .constant c => c
  | .connective F formulas =>
      F fun i ↦ realize (formulas i) M rows parameters
  | .iSupRow formula =>
      ⨆ x : M.Row, realize formula M (Fin.cons x rows) parameters
  | .iInfRow formula =>
      ⨅ x : M.Row, realize formula M (Fin.cons x rows) parameters
  | .iSupParameter formula =>
      ⨆ y : M.Parameter, realize formula M rows (Fin.cons y parameters)
  | .iInfParameter formula =>
      ⨅ y : M.Parameter, realize formula M rows (Fin.cons y parameters)

/-- The real-valued interpretation of a formula with one free variable of
each sort. -/
def binaryValue (φ : Formula 1 1) (M : Structure) : M.Row → M.Parameter → ℝ :=
  fun x y ↦ (φ.realize M (fun _ ↦ x) (fun _ ↦ y) : ℝ)

/-- The atomic binary predicate as a formula with one variable of each sort. -/
def atomic : Formula 1 1 := .predicate 0 0

@[simp]
theorem atomic_binaryValue (M : Structure) :
    atomic.binaryValue M = fun x y ↦ (M.predicate x y : ℝ) := by
  rfl

end Formula

/-- A sentence has no free variables. -/
abbrev Sentence := Formula 0 0

namespace Sentence

/-- The truth value of a sentence in a structure. -/
def value (φ : Sentence) (M : Structure) : TruthValue :=
  φ.realize M Fin.elim0 Fin.elim0

end Sentence

/-- Two structures have the same complete theory when every sentence in the
fragment has the same truth value in both. -/
def SameCompleteTheory (M : Structure.{u, v}) (N : Structure.{u', v'}) : Prop :=
  ∀ φ : Sentence, φ.value M = φ.value N

namespace SameCompleteTheory


end SameCompleteTheory

/-- One infinite low/high independence witness for a formula in a bounded
structure. -/
def HasInfiniteIPWitness
    (M : Structure.{u, v}) (φ : Formula 1 1) (low high : ℝ) : Prop :=
  ∃ rows : ℕ → M.Row,
    ∀ E F : Finset ℕ, Disjoint E F →
      ∃ b : M.Parameter,
        (∀ i ∈ E, φ.binaryValue M (rows i) b ≤ low) ∧
        (∀ i ∈ F, high ≤ φ.binaryValue M (rows i) b)

/-- Semantic IP in the complete theory: the formula has an infinite IP
witness in some structure agreeing on the value of every sentence. -/
def HasIPInCompleteTheory (M : Structure.{u, v})
    (φ : Formula 1 1) : Prop :=
  ∃ N : Structure.{u, v}, SameCompleteTheory M N ∧
    ∃ low high : ℝ, low < high ∧ HasInfiniteIPWitness N φ low high

/-- Fixed-gap finite patterns inside a bounded structure.  No external norm
bounds are needed because the two carriers are already the chosen sorts. -/
def HasFiniteIPPatternsInEveryDimension
    (M : Structure.{u, v}) (φ : Formula 1 1) (low high : ℝ) : Prop :=
  ∀ n : ℕ, ∃ rows : Fin n → M.Row,
    IsIPPattern (fun i y ↦ φ.binaryValue M (rows i) y) low high


/-- The atomic-only compactness principle needed by the norm-formula
application.  Keeping this smaller proposition separate makes the first
vertical slice no stronger than the paper requires. -/
def AtomicFinitePatternCompactness (M : Structure.{u, v}) : Prop :=
  ∀ (low high : ℝ), low < high →
    HasFiniteIPPatternsInEveryDimension M Formula.atomic low high →
    HasIPInCompleteTheory M Formula.atomic


end

end NormFormula.ContinuousLogic
