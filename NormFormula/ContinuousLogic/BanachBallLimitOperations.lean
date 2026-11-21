import NormFormula.ContinuousLogic.BanachBallWitnessLimitClosure

/-!
# Typed Banach operations inside the ball-sorted stage limit

Every algebraic request at a finite stage is adjoined at the next stage and
hence determines a canonical limit index.  This realizes zero, inclusions,
negation, addition, and rational scalar multiplication inside the dense
witness limit, with exactly the corresponding ambient values.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u w

namespace BallWitnessIndexing

variable {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
  {M : BallStructure.{u, w} Symbol symbolRadius}

/-- Package one algebraic request over a finite stage as a successor-stage
limit index in its computed output radius. -/
def limitOperation [Encodable Symbol] (initial : BallWitnessIndexing M)
    (stage : ℕ)
    (request : BallOperationRequest (initial.iterate stage).Index) :
    initial.LimitIndex request.outputRadius :=
  ⟨stage + 1, (initial.iterate stage).operated request⟩

@[simp]
theorem limitMap_limitOperation [Encodable Symbol]
    (initial : BallWitnessIndexing M) (stage : ℕ)
    (request : BallOperationRequest (initial.iterate stage).Index) :
    initial.limitMap request.outputRadius
        (initial.limitOperation stage request) =
      request.value M (initial.iterate stage).indexMap :=
  rfl

/-- The distinguished zero of every radius sort belongs to the limit. -/
def limitZero [Encodable Symbol] (initial : BallWitnessIndexing M)
    (radius : ℚ≥0) : initial.LimitIndex radius :=
  initial.limitOperation 0 (BallOperationRequest.zero radius)

@[simp]
theorem limitMap_limitZero [Encodable Symbol]
    (initial : BallWitnessIndexing M) (radius : ℚ≥0) :
    initial.limitMap radius (initial.limitZero radius) = M.zero radius := by
  simpa only [limitZero, BallOperationRequest.outputRadius_zero,
    BallOperationRequest.value_zero] using
    initial.limitMap_limitOperation 0
      (BallOperationRequest.zero (Index := (initial.iterate 0).Index) radius)

/-- Inclusion of a limit point into a larger rational radius remains a limit
point. -/
def limitInclusion [Encodable Symbol] (initial : BallWitnessIndexing M)
    {r s : ℚ≥0} (h : r ≤ s) (index : initial.LimitIndex r) :
    initial.LimitIndex s :=
  initial.limitOperation index.1
    (BallOperationRequest.inclusion h index.2)

@[simp]
theorem limitMap_limitInclusion [Encodable Symbol]
    (initial : BallWitnessIndexing M) {r s : ℚ≥0} (h : r ≤ s)
    (index : initial.LimitIndex r) :
    initial.limitMap s (initial.limitInclusion h index) =
      M.inclusion h (initial.limitMap r index) := by
  simpa only [limitInclusion, BallOperationRequest.outputRadius_inclusion,
    BallOperationRequest.value_inclusion, limitMap] using
    initial.limitMap_limitOperation index.1
      (BallOperationRequest.inclusion h index.2)

/-- Negation of a limit point remains a limit point in the same radius. -/
def limitNeg [Encodable Symbol] (initial : BallWitnessIndexing M)
    (radius : ℚ≥0) (index : initial.LimitIndex radius) :
    initial.LimitIndex radius :=
  initial.limitOperation index.1
    (BallOperationRequest.neg radius index.2)

@[simp]
theorem limitMap_limitNeg [Encodable Symbol]
    (initial : BallWitnessIndexing M) (radius : ℚ≥0)
    (index : initial.LimitIndex radius) :
    initial.limitMap radius (initial.limitNeg radius index) =
      M.neg radius (initial.limitMap radius index) := by
  simpa only [limitNeg, BallOperationRequest.outputRadius_neg,
    BallOperationRequest.value_neg, limitMap] using
    initial.limitMap_limitOperation index.1
      (BallOperationRequest.neg radius index.2)

/-- Add two limit points after lifting their indices to one common finite
stage. -/
def limitAdd [Encodable Symbol] (initial : BallWitnessIndexing M)
    (r s : ℚ≥0) (left : initial.LimitIndex r)
    (right : initial.LimitIndex s) : initial.LimitIndex (r + s) :=
  initial.limitOperation (max left.1 right.1)
    (BallOperationRequest.add r s
      (initial.liftTo (Nat.le_max_left left.1 right.1) r left.2)
      (initial.liftTo (Nat.le_max_right left.1 right.1) s right.2))

@[simp]
theorem limitMap_limitAdd [Encodable Symbol]
    (initial : BallWitnessIndexing M) (r s : ℚ≥0)
    (left : initial.LimitIndex r) (right : initial.LimitIndex s) :
    initial.limitMap (r + s) (initial.limitAdd r s left right) =
      M.add r s
        (initial.limitMap r left, initial.limitMap s right) := by
  simpa only [limitAdd, BallOperationRequest.outputRadius_add,
    BallOperationRequest.value_add, indexMap_liftTo, limitMap] using
    initial.limitMap_limitOperation (max left.1 right.1)
      (BallOperationRequest.add r s
        (initial.liftTo (Nat.le_max_left left.1 right.1) r left.2)
        (initial.liftTo (Nat.le_max_right left.1 right.1) s right.2))

/-- Every rational scalar multiple of a limit point remains a limit point in
the exact output radius. -/
def limitSmul [Encodable Symbol] (initial : BallWitnessIndexing M)
    (q : ℚ) (radius : ℚ≥0) (index : initial.LimitIndex radius) :
    initial.LimitIndex (q.nnabs * radius) :=
  initial.limitOperation index.1
    (BallOperationRequest.smul q radius index.2)

@[simp]
theorem limitMap_limitSmul [Encodable Symbol]
    (initial : BallWitnessIndexing M) (q : ℚ) (radius : ℚ≥0)
    (index : initial.LimitIndex radius) :
    initial.limitMap (q.nnabs * radius)
        (initial.limitSmul q radius index) =
      M.smul q radius (initial.limitMap radius index) := by
  simpa only [limitSmul, BallOperationRequest.outputRadius_smul,
    BallOperationRequest.value_smul, limitMap] using
    initial.limitMap_limitOperation index.1
      (BallOperationRequest.smul q radius index.2)

end BallWitnessIndexing

end

end NormFormula.ContinuousLogic
