import NormFormula.ContinuousLogic.BanachBallReducedPredicate
import NormFormula.ContinuousLogic.BanachBallTermLos

/-!
# Atomic and connective Łoś theorems for rational-ball formulas

This file packages the desired reduced-product Łoś equality as a property of
a typed ball formula.  It proves the property for both atomic constructors,
constants, and arbitrary finitary continuous connectives.  Equivalently,
every quantifier-free typed formula satisfies Łoś.  The remaining formula
constructors are the radius-tagged supremum and infimum quantifiers.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u w

namespace BallFormula

variable {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
variable (M : BallStructure.{u, w} Symbol symbolRadius)

/-- The Łoś equality for one typed ball formula at every assignment of
sequence representatives. -/
def HasReducedProductLos {n : ℕ} {context : BallContext n}
    (formula : BallFormula Symbol symbolRadius context) : Prop :=
  ∀ assignment : BallTerm.ReducedAssignment M.toRationalBallSystem context,
    formula.realize M.reducedProduct
        (BallTerm.completedAssignment M.toRationalBallSystem assignment) =
      ultralimit fun k ↦ formula.realize M
        (BallTerm.coordinateAssignment M.toRationalBallSystem assignment k)

/-- Łoś for normalized-distance atoms follows from term Łoś and the exact
distance law on completed representatives. -/
theorem hasReducedProductLos_distance {n : ℕ} {context : BallContext n}
    {r : ℚ≥0} (left right : BallTerm context r) :
    HasReducedProductLos M (.distance left right) := by
  intro assignment
  rw [realize_distance,
    show left.realize M.reducedProduct.toRationalBallSystem
        (BallTerm.completedAssignment M.toRationalBallSystem assignment) =
      ReducedProduct.completedMk (M.toRationalBallSystem.reducedBound r)
        (fun k ↦ left.realize M.toRationalBallSystem
          (BallTerm.coordinateAssignment M.toRationalBallSystem assignment k)) from
      BallTerm.realize_reducedProduct M.toRationalBallSystem left assignment,
    show right.realize M.reducedProduct.toRationalBallSystem
        (BallTerm.completedAssignment M.toRationalBallSystem assignment) =
      ReducedProduct.completedMk (M.toRationalBallSystem.reducedBound r)
        (fun k ↦ right.realize M.toRationalBallSystem
          (BallTerm.coordinateAssignment M.toRationalBallSystem assignment k)) from
      BallTerm.realize_reducedProduct M.toRationalBallSystem right assignment,
    ballReducedProduct_distance_mk]
  rfl

/-- Łoś for named-predicate atoms follows from term Łoś and predicate descent. -/
theorem hasReducedProductLos_predicate {n : ℕ} {context : BallContext n}
    (symbol : Symbol) (term : BallTerm context (symbolRadius symbol)) :
    HasReducedProductLos M (.predicate symbol term) := by
  intro assignment
  rw [realize_predicate,
    show term.realize M.reducedProduct.toRationalBallSystem
        (BallTerm.completedAssignment M.toRationalBallSystem assignment) =
      ReducedProduct.completedMk
        (M.toRationalBallSystem.reducedBound (symbolRadius symbol))
        (fun k ↦ term.realize M.toRationalBallSystem
          (BallTerm.coordinateAssignment M.toRationalBallSystem assignment k)) from
      BallTerm.realize_reducedProduct M.toRationalBallSystem term assignment,
    ballReducedProduct_predicate_mk]
  rfl

/-- Constant formulas satisfy Łoś. -/
theorem hasReducedProductLos_constant {n : ℕ} {context : BallContext n}
    (value : TruthValue) :
    HasReducedProductLos M (.constant value : BallFormula Symbol symbolRadius context) := by
  intro _assignment
  exact (ultralimit_const value).symm

/-- The Łoś property is closed under every finitary continuous connective. -/
theorem hasReducedProductLos_connective {n : ℕ} {context : BallContext n}
    {arity : ℕ} (gate : Connective arity)
    (children : Fin arity → BallFormula Symbol symbolRadius context)
    (hchildren : ∀ i, HasReducedProductLos M (children i)) :
    HasReducedProductLos M (.connective gate children) := by
  intro assignment
  change gate (fun i ↦ (children i).realize M.reducedProduct
      (BallTerm.completedAssignment M.toRationalBallSystem assignment)) = _
  rw [show (fun i ↦ (children i).realize M.reducedProduct
      (BallTerm.completedAssignment M.toRationalBallSystem assignment)) =
      (fun i ↦ ultralimit fun k ↦ (children i).realize M
        (BallTerm.coordinateAssignment M.toRationalBallSystem assignment k)) by
    funext i
    exact hchildren i assignment]
  exact (ultralimit_connective gate fun i k ↦ (children i).realize M
    (BallTerm.coordinateAssignment M.toRationalBallSystem assignment k)).symm

/-- Syntactic quantifier-freeness for typed ball formulas. -/
inductive IsQuantifierFree :
    {n : ℕ} → {context : BallContext n} →
      BallFormula Symbol symbolRadius context → Prop
  | distance {n : ℕ} {context : BallContext n} {r : ℚ≥0}
      (left right : BallTerm context r) : IsQuantifierFree (.distance left right)
  | predicate {n : ℕ} {context : BallContext n} (symbol : Symbol)
      (term : BallTerm context (symbolRadius symbol)) :
      IsQuantifierFree (.predicate symbol term)
  | constant {n : ℕ} {context : BallContext n} (value : TruthValue) :
      IsQuantifierFree (.constant value)
  | connective {n : ℕ} {context : BallContext n} {arity : ℕ}
      (gate : Connective arity)
      (children : Fin arity → BallFormula Symbol symbolRadius context)
      (hchildren : ∀ i, IsQuantifierFree (children i)) :
      IsQuantifierFree (.connective gate children)


end BallFormula

end


end NormFormula.ContinuousLogic
