import NormFormula.ContinuousLogic.BanachBallFormula
import NormFormula.ContinuousLogic.BanachBallReducedProduct

/-!
# Named predicates on completed rational-ball reduced products

The operation layer of a completed rational-ball reduced product is supplied
by `BanachBallReducedProduct`.  Here each typed unary predicate is interpreted
on sequence representatives by its truth-value ultralimit.  Uniform
continuity first descends this interpretation to the metric separation
quotient and then extends it uniquely to the completed sort.

The resulting `BallStructure` has exact atomic computation laws on sequence
representatives and on the diagonal copy of the original structure.  We also
record the corresponding law for normalized distance atoms.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Filter UniformSpace
open scoped Topology

universe u w

variable {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
variable (M : BallStructure.{u, w} Symbol symbolRadius)

/-- Interpret a named ball predicate coordinatewise and take its truth-value
ultralimit before quotienting or completing the sort. -/
def ballReducedPredicateOnSequences (symbol : Symbol)
    (x : ReducedSequence (M.toRationalBallSystem.reducedBound (symbolRadius symbol))) :
    TruthValue :=
  ultralimit fun n ↦ M.predicate symbol (x n)

set_option maxHeartbeats 400000 in
/-- A coordinatewise predicate ultralimit is uniformly continuous for the
normalized sequence pseudometric. -/
theorem ballReducedPredicateOnSequences_uniformContinuous (symbol : Symbol) :
    UniformContinuous (ballReducedPredicateOnSequences M symbol) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨η, hη, hmodulus⟩ := Metric.uniformContinuous_iff.1
    (M.predicate_uniformContinuous symbol) (ε / 2) (half_pos hε)
  let B := M.toRationalBallSystem.reducedBound (symbolRadius symbol)
  let δ := η / B.scale
  have hδ : 0 < δ := div_pos hη B.scale_pos
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  have hcoordinate : ∀ᶠ n in indexUltrafilter, dist (x n) (y n) < η := by
    have hnormalized :=
      (ReducedSequence.tendsto_normalizedDistance B x y).eventually_lt_const hxy
    filter_upwards [hnormalized] with n hn
    exact (div_lt_div_iff_of_pos_right B.scale_pos).1 hn
  have houtput : ∀ᶠ n in indexUltrafilter,
      dist (M.predicate symbol (x n)) (M.predicate symbol (y n)) ≤ ε / 2 := by
    filter_upwards [hcoordinate] with n hn
    exact (hmodulus hn).le
  have hlimit : Tendsto
      (fun n ↦ dist (M.predicate symbol (x n)) (M.predicate symbol (y n)))
      indexUltrafilter
      (𝓝 (dist (ballReducedPredicateOnSequences M symbol x)
        (ballReducedPredicateOnSequences M symbol y))) :=
    (tendsto_ultralimit fun n ↦ M.predicate symbol (x n)).dist
      (tendsto_ultralimit fun n ↦ M.predicate symbol (y n))
  exact (isClosed_Iic.mem_of_tendsto hlimit houtput).trans_lt (half_lt_self hε)

/-- Descend one coordinatewise predicate ultralimit to the normalized metric
reduced product. -/
def ballReducedPredicateOnQuotient (symbol : Symbol) :
    ReducedProduct (M.toRationalBallSystem.reducedBound (symbolRadius symbol)) → TruthValue :=
  SeparationQuotient.lift' (ballReducedPredicateOnSequences M symbol)

@[simp]
theorem ballReducedPredicateOnQuotient_mk (symbol : Symbol)
    (x : ReducedSequence
      (M.toRationalBallSystem.reducedBound (symbolRadius symbol))) :
    ballReducedPredicateOnQuotient M symbol
        (ReducedProduct.mk
          (M.toRationalBallSystem.reducedBound (symbolRadius symbol)) x) =
      ballReducedPredicateOnSequences M symbol x := by
  exact SeparationQuotient.lift'_mk
    (ballReducedPredicateOnSequences_uniformContinuous M symbol) x

/-- The predicate on the quotient sort is uniformly continuous. -/
theorem ballReducedPredicateOnQuotient_uniformContinuous (symbol : Symbol) :
    UniformContinuous (ballReducedPredicateOnQuotient M symbol) :=
  SeparationQuotient.uniformContinuous_lift' _

/-- Extend one quotient predicate to the completed reduced ball. -/
def completedBallReducedPredicate (symbol : Symbol) :
    (M.toRationalBallSystem.reducedProduct).Ball (symbolRadius symbol) → TruthValue :=
  Completion.extension (ballReducedPredicateOnQuotient M symbol)

/-- The completed predicate remains uniformly continuous. -/
theorem completedBallReducedPredicate_uniformContinuous (symbol : Symbol) :
    UniformContinuous (completedBallReducedPredicate M symbol) :=
  Completion.uniformContinuous_extension

@[simp]
theorem completedBallReducedPredicate_mk (symbol : Symbol)
    (x : ReducedSequence
      (M.toRationalBallSystem.reducedBound (symbolRadius symbol))) :
    completedBallReducedPredicate M symbol
        (ReducedProduct.completedMk
          (M.toRationalBallSystem.reducedBound (symbolRadius symbol)) x) =
      ultralimit (fun n ↦ M.predicate symbol (x n)) := by
  rw [completedBallReducedPredicate, ReducedProduct.completedMk,
    Completion.extension_coe
      (ballReducedPredicateOnQuotient_uniformContinuous M symbol),
    ballReducedPredicateOnQuotient_mk]
  rfl

/-- The completed reduced product in the full typed ball language. -/
def BallStructure.reducedProduct : BallStructure.{u, w} Symbol symbolRadius where
  toRationalBallSystem := M.toRationalBallSystem.reducedProduct
  predicate := completedBallReducedPredicate M
  predicate_uniformContinuous := completedBallReducedPredicate_uniformContinuous M

@[simp]
theorem ballReducedProduct_predicate_mk (symbol : Symbol)
    (x : ReducedSequence
      (M.toRationalBallSystem.reducedBound (symbolRadius symbol))) :
    M.reducedProduct.predicate symbol
        (ReducedProduct.completedMk
          (M.toRationalBallSystem.reducedBound (symbolRadius symbol)) x) =
      ultralimit (fun n ↦ M.predicate symbol (x n)) :=
  completedBallReducedPredicate_mk M symbol x


/-- Normalized distance on completed reduced representatives is the
ultralimit of the original normalized coordinate distances. -/
@[simp]
theorem ballReducedProduct_distance_mk (r : ℚ≥0)
    (x y : ReducedSequence (M.toRationalBallSystem.reducedBound r)) :
    normalizedBallDistanceTruth M.reducedProduct.toRationalBallSystem r
        (ReducedProduct.completedMk (M.toRationalBallSystem.reducedBound r) x)
        (ReducedProduct.completedMk (M.toRationalBallSystem.reducedBound r) y) =
      ultralimit
        (fun n ↦ normalizedBallDistanceTruth M.toRationalBallSystem r (x n) (y n)) := by
  ext
  change dist
      (show Completion (ReducedProduct (M.toRationalBallSystem.reducedBound r)) from
        (ReducedProduct.mk (M.toRationalBallSystem.reducedBound r) x :
          Completion (ReducedProduct (M.toRationalBallSystem.reducedBound r))))
      (show Completion (ReducedProduct (M.toRationalBallSystem.reducedBound r)) from
        (ReducedProduct.mk (M.toRationalBallSystem.reducedBound r) y :
          Completion (ReducedProduct (M.toRationalBallSystem.reducedBound r)))) /
        1 = _
  rw [div_one, Completion.dist_eq, ReducedProduct.dist_mk]
  rfl


end


end NormFormula.ContinuousLogic
