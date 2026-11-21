import NormFormula.ContinuousLogic.BanachBallTerm
import NormFormula.ContinuousLogic.Basic

/-!
# Typed formulae over rational-radius Banach balls

This file adds the predicate and formula layer over `BallTerm`.  A structure
may name any family of unary predicates, each assigned to one rational-radius
sort.  Atomic formulae are normalized distances between same-sort terms or a
named predicate applied to a term.  Continuous connectives and sup/inf
quantifiers over explicitly chosen ball sorts complete the syntax.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open scoped Topology

universe u v w

/-- A rational ball system expanded by typed uniformly continuous unary
predicates. -/
structure BallStructure (Symbol : Type w) (symbolRadius : Symbol → ℚ≥0)
    extends RationalBallSystem.{u} where
  predicate : ∀ symbol : Symbol, Ball (symbolRadius symbol) → TruthValue
  predicate_uniformContinuous : ∀ symbol : Symbol,
    UniformContinuous (predicate symbol)

/-- Normalized distance on one bounded sort. -/
def normalizedBallDistanceTruth (S : RationalBallSystem.{u}) (r : ℚ≥0)
    (x y : S.Ball r) : TruthValue := by
  refine ⟨dist x y / S.sortBound r,
    div_nonneg dist_nonneg (S.sortBound_pos r).le, ?_⟩
  exact (div_le_one (S.sortBound_pos r)).2 (S.dist_le_sortBound r x y)

@[simp]
theorem normalizedBallDistanceTruth_coe
    (S : RationalBallSystem.{u}) (r : ℚ≥0) (x y : S.Ball r) :
    (normalizedBallDistanceTruth S r x y : ℝ) =
      dist x y / S.sortBound r :=
  rfl

/-- Normalized distance is uniformly continuous in both arguments. -/
theorem normalizedBallDistanceTruth_uniformContinuous
    (S : RationalBallSystem.{u}) (r : ℚ≥0) :
    UniformContinuous fun p : S.Ball r × S.Ball r ↦
      normalizedBallDistanceTruth S r p.1 p.2 :=
  (uniformContinuous_dist.div_const' (S.sortBound r)).subtype_mk _

/-- Typed continuous formulae over a finite context of rational ball sorts. -/
inductive BallFormula (Symbol : Type w) (symbolRadius : Symbol → ℚ≥0) :
    {n : ℕ} → BallContext n → Type max 1 w
  | distance {n : ℕ} {context : BallContext n} {r : ℚ≥0} :
      BallTerm context r → BallTerm context r →
        BallFormula Symbol symbolRadius context
  | predicate {n : ℕ} {context : BallContext n} (symbol : Symbol) :
      BallTerm context (symbolRadius symbol) →
        BallFormula Symbol symbolRadius context
  | constant {n : ℕ} {context : BallContext n} :
      TruthValue → BallFormula Symbol symbolRadius context
  | connective {n : ℕ} {context : BallContext n} {arity : ℕ} : Connective arity →
      (Fin arity → BallFormula Symbol symbolRadius context) →
        BallFormula Symbol symbolRadius context
  | iSup {n : ℕ} {context : BallContext n} (r : ℚ≥0) :
      BallFormula Symbol symbolRadius (Fin.cons r context) →
        BallFormula Symbol symbolRadius context
  | iInf {n : ℕ} {context : BallContext n} (r : ℚ≥0) :
      BallFormula Symbol symbolRadius (Fin.cons r context) →
        BallFormula Symbol symbolRadius context

namespace BallFormula

/-- Evaluation of a typed ball formula. -/
def realize {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius)
    {n : ℕ} {context : BallContext n} :
    BallFormula Symbol symbolRadius context →
      BallTerm.Assignment M.toRationalBallSystem context → TruthValue
  | .distance (r := r) left right, assignment =>
      normalizedBallDistanceTruth M.toRationalBallSystem r
        (left.realize M.toRationalBallSystem assignment)
        (right.realize M.toRationalBallSystem assignment)
  | .predicate symbol term, assignment =>
      M.predicate symbol (term.realize M.toRationalBallSystem assignment)
  | .constant value, _assignment => value
  | .connective gate children, assignment =>
      gate fun i ↦ (children i).realize M assignment
  | .iSup r formula, assignment =>
      ⨆ x : M.Ball r, formula.realize M (Fin.cons x assignment)
  | .iInf r formula, assignment =>
      ⨅ x : M.Ball r, formula.realize M (Fin.cons x assignment)

@[simp]
theorem realize_distance {Symbol : Type w}
    {symbolRadius : Symbol → ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius)
    {n : ℕ} {context : BallContext n} {r : ℚ≥0}
    (left right : BallTerm context r)
    (assignment : BallTerm.Assignment M.toRationalBallSystem context) :
    (BallFormula.distance left right).realize M assignment =
      normalizedBallDistanceTruth M.toRationalBallSystem r
        (left.realize M.toRationalBallSystem assignment)
        (right.realize M.toRationalBallSystem assignment) :=
  rfl

@[simp]
theorem realize_predicate {Symbol : Type w}
    {symbolRadius : Symbol → ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius)
    {n : ℕ} {context : BallContext n} (symbol : Symbol)
    (term : BallTerm context (symbolRadius symbol))
    (assignment : BallTerm.Assignment M.toRationalBallSystem context) :
    (BallFormula.predicate symbol term).realize M assignment =
      M.predicate symbol (term.realize M.toRationalBallSystem assignment) :=
  rfl

@[simp]
theorem realize_constant {Symbol : Type w}
    {symbolRadius : Symbol → ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius)
    {n : ℕ} {context : BallContext n} (value : TruthValue)
    (assignment : BallTerm.Assignment M.toRationalBallSystem context) :
    (BallFormula.constant value : BallFormula Symbol symbolRadius context).realize
      M assignment = value :=
  rfl

@[simp]
theorem realize_connective {Symbol : Type w}
    {symbolRadius : Symbol → ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius)
    {n : ℕ} {context : BallContext n} {arity : ℕ}
    (connective : Connective arity)
    (formulas : Fin arity → BallFormula Symbol symbolRadius context)
    (assignment : BallTerm.Assignment M.toRationalBallSystem context) :
    (BallFormula.connective connective formulas).realize M assignment =
      connective fun i ↦ (formulas i).realize M assignment :=
  rfl

@[simp]
theorem realize_iSup {Symbol : Type w}
    {symbolRadius : Symbol → ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius)
    {n : ℕ} {context : BallContext n} (r : ℚ≥0)
    (formula : BallFormula Symbol symbolRadius (Fin.cons r context))
    (assignment : BallTerm.Assignment M.toRationalBallSystem context) :
    (BallFormula.iSup r formula).realize M assignment =
      ⨆ x : M.Ball r, formula.realize M (Fin.cons x assignment) :=
  rfl

@[simp]
theorem realize_iInf {Symbol : Type w}
    {symbolRadius : Symbol → ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius)
    {n : ℕ} {context : BallContext n} (r : ℚ≥0)
    (formula : BallFormula Symbol symbolRadius (Fin.cons r context))
    (assignment : BallTerm.Assignment M.toRationalBallSystem context) :
    (BallFormula.iInf r formula).realize M assignment =
      ⨅ x : M.Ball r, formula.realize M (Fin.cons x assignment) :=
  rfl

/-- A typed distance atom is uniformly continuous in its assignment. -/
theorem distance_realize_uniformContinuous
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius)
    {n : ℕ} {context : BallContext n} {r : ℚ≥0}
    (left right : BallTerm context r) :
    UniformContinuous fun assignment =>
      (BallFormula.distance left right).realize M assignment :=
  (normalizedBallDistanceTruth_uniformContinuous M.toRationalBallSystem r).comp
    ((left.realize_uniformContinuous M.toRationalBallSystem).prodMk
      (right.realize_uniformContinuous M.toRationalBallSystem))

/-- A named predicate atom is uniformly continuous in its assignment. -/
theorem predicate_realize_uniformContinuous
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius)
    {n : ℕ} {context : BallContext n} (symbol : Symbol)
    (term : BallTerm context (symbolRadius symbol)) :
    UniformContinuous fun assignment =>
      (BallFormula.predicate symbol term).realize M assignment :=
  (M.predicate_uniformContinuous symbol).comp
    (term.realize_uniformContinuous M.toRationalBallSystem)

end BallFormula

/-- A sentence has no free ball variables. -/
abbrev BallSentence (Symbol : Type w) (symbolRadius : Symbol → ℚ≥0) :=
  BallFormula Symbol symbolRadius (Fin.elim0 : BallContext 0)

namespace BallSentence

/-- The value of a typed ball sentence. -/
def value {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    (sentence : BallSentence Symbol symbolRadius)
    (M : BallStructure.{u, w} Symbol symbolRadius) : TruthValue :=
  sentence.realize M (fun i : Fin 0 ↦ nomatch i)

end BallSentence

/-- Equality of complete theories in the typed ball-sorted language. -/
def BallSameCompleteTheory {Symbol : Type w}
    {symbolRadius : Symbol → ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius)
    (N : BallStructure.{v, w} Symbol symbolRadius) : Prop :=
  ∀ sentence : BallSentence Symbol symbolRadius,
    sentence.value M = sentence.value N

/-- The predicate-free Banach ball language. -/
inductive EmptyBallPredicate

/-- Radius assignment for the empty predicate alphabet. -/
def emptyBallPredicateRadius : EmptyBallPredicate → ℚ≥0 :=
  nofun

/-- The standard predicate-free ball structure of a real Banach space. -/
def standardBanachBallStructure
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] :
    BallStructure EmptyBallPredicate emptyBallPredicateRadius where
  toRationalBallSystem := standardRationalBallSystem (E := E)
  predicate := nofun
  predicate_uniformContinuous := nofun

/-- In the standard Banach structure, a typed distance atom is exactly the
normalized ambient norm distance between its term values. -/
theorem standard_distance_formula_value
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℕ} {context : BallContext n} {r : ℚ≥0}
    (left right : BallTerm context r)
    (assignment : BallTerm.Assignment
      (standardRationalBallSystem (E := E)) context) :
    ((BallFormula.distance left right :
        BallFormula EmptyBallPredicate emptyBallPredicateRadius context).realize
      (standardBanachBallStructure E) assignment : ℝ) =
      dist (left.standardValue assignment) (right.standardValue assignment) /
        rationalBallMetricBound r := by
  rfl

end

end NormFormula.ContinuousLogic
