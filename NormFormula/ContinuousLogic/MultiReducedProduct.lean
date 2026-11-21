import NormFormula.ContinuousLogic.MultiPredicate
import NormFormula.ContinuousLogic.ReducedProduct

/-!
# Reduced products for a many-predicate language

The metric carriers of a reduced product do not depend on the predicate
alphabet.  For each symbol we therefore apply the one-predicate construction
to the corresponding reduct and assemble the resulting predicates into a
`MultiStructure`.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u v w

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.parameterPseudoMetricSpace MultiStructure.rowNonempty
  MultiStructure.parameterNonempty Structure.rowPseudoMetricSpace
  Structure.parameterPseudoMetricSpace Structure.rowNonempty
  Structure.parameterNonempty

namespace MultiStructure

/-- Forget every predicate except one selected symbol. -/
def singlePredicate {Symbol : Type w} (M : MultiStructure.{u, v, w} Symbol)
    (symbol : Symbol) : Structure.{u, v} where
  Row := M.Row
  Parameter := M.Parameter
  rowPseudoMetricSpace := M.rowPseudoMetricSpace
  parameterPseudoMetricSpace := M.parameterPseudoMetricSpace
  rowNonempty := M.rowNonempty
  parameterNonempty := M.parameterNonempty
  predicate := M.predicate symbol
  predicate_uniformContinuous := M.predicate_uniformContinuous symbol

/-- Bounded scales for the two metric sorts of a many-predicate structure. -/
structure Bounds {Symbol : Type w} (M : MultiStructure.{u, v, w} Symbol) where
  row : BoundedMetricSort M.Row
  parameter : BoundedMetricSort M.Parameter

namespace Bounds

/-- The same carrier bounds, viewed on a one-predicate reduct. -/
def singlePredicate {Symbol : Type w} {M : MultiStructure.{u, v, w} Symbol}
    (bounds : M.Bounds) (symbol : Symbol) :
    (M.singlePredicate symbol).Bounds where
  row := bounds.row
  parameter := bounds.parameter

end Bounds

end MultiStructure

variable {Symbol : Type w} (M : MultiStructure.{u, v, w} Symbol)
  (bounds : M.Bounds)

/-- Interpret one symbol coordinatewise and take its truth-value ultralimit
before passing to the metric separation quotients. -/
def multiReducedPredicateOnSequences (symbol : Symbol)
    (x : ReducedSequence bounds.row)
    (y : ReducedSequence bounds.parameter) : TruthValue :=
  reducedPredicateOnSequences (M.singlePredicate symbol)
    (bounds.singlePredicate symbol) x y

/-- The predicate associated with one symbol on the quotient sorts. -/
def multiReducedPredicate (symbol : Symbol) :
    ReducedProduct bounds.row → ReducedProduct bounds.parameter → TruthValue :=
  reducedPredicate (M.singlePredicate symbol)
    (bounds.singlePredicate symbol)

@[simp]
theorem multiReducedPredicate_mk (symbol : Symbol)
    (x : ReducedSequence bounds.row)
    (y : ReducedSequence bounds.parameter) :
    multiReducedPredicate M bounds symbol (ReducedProduct.mk bounds.row x)
      (ReducedProduct.mk bounds.parameter y) =
      ultralimit (fun n ↦ M.predicate symbol (x n) (y n)) :=
  reducedPredicate_mk (M.singlePredicate symbol)
    (bounds.singlePredicate symbol) x y

/-- Every symbol remains uniformly continuous after passage to the quotient
sorts. -/
theorem multiReducedPredicate_uniformContinuous (symbol : Symbol) :
    UniformContinuous
      (fun p : ReducedProduct bounds.row × ReducedProduct bounds.parameter ↦
        multiReducedPredicate M bounds symbol p.1 p.2) :=
  reducedPredicate_uniformContinuous (M.singlePredicate symbol)
    (bounds.singlePredicate symbol)

/-- The bounded metric reduced product in an arbitrary many-predicate
language. -/
def MultiStructure.reducedProduct : MultiStructure.{u, v, w} Symbol where
  Row := ReducedProduct bounds.row
  Parameter := ReducedProduct bounds.parameter
  rowPseudoMetricSpace := inferInstance
  parameterPseudoMetricSpace := inferInstance
  rowNonempty := inferInstance
  parameterNonempty := inferInstance
  predicate := multiReducedPredicate M bounds
  predicate_uniformContinuous := multiReducedPredicate_uniformContinuous M bounds

/-- The diagonal maps preserve every distinguished predicate. -/
@[simp]
theorem multiReducedProduct_predicate_const (symbol : Symbol)
    (x : M.Row) (y : M.Parameter) :
    (M.reducedProduct bounds).predicate symbol
      (ReducedProduct.const bounds.row x)
      (ReducedProduct.const bounds.parameter y) = M.predicate symbol x y := by
  change ultralimit (fun _ : ℕ ↦ M.predicate symbol x y) =
    M.predicate symbol x y
  exact ultralimit_const (M.predicate symbol x y)

end

end NormFormula.ContinuousLogic
