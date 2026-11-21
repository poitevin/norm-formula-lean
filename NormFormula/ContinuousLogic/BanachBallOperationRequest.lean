import NormFormula.ContinuousLogic.BanachBallWitnessRequest

/-!
# Countable typed requests for the Banach-ball operations

Witness closure alone does not ensure that the generated limit sorts carry
the language's function symbols.  This file gives a countable request type
for one application of zero, inclusion, negation, addition, or rational
scalar multiplication to a dependent family of current indices.  Every
request records its output radius and evaluates in exactly that ambient sort.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u v w

/-- A countable code for applying one typed Banach-ball operation to current
indices.  The five summands encode zero, inclusion, negation, addition, and
rational scalar multiplication, respectively. -/
def BallOperationRequest (Index : ℚ≥0 → Type v) :=
  ℚ≥0 ⊕
    (Σ r : ℚ≥0, Σ s : ℚ≥0, PLift (r ≤ s) × Index r) ⊕
    (Σ r : ℚ≥0, Index r) ⊕
    (Σ r : ℚ≥0, Σ s : ℚ≥0, Index r × Index s) ⊕
    (ℚ × (Σ r : ℚ≥0, Index r))

noncomputable instance ballOperationRequest_countable
    (Index : ℚ≥0 → Type v) [∀ radius, Countable (Index radius)] :
    Countable (BallOperationRequest Index) := by
  unfold BallOperationRequest
  infer_instance

namespace BallOperationRequest

variable {Index : ℚ≥0 → Type v}

/-- Request the distinguished zero in one radius sort. -/
def zero (radius : ℚ≥0) : BallOperationRequest Index :=
  Sum.inl radius

/-- Request an inclusion of a current point into a larger radius sort. -/
def inclusion {r s : ℚ≥0} (h : r ≤ s) (index : Index r) :
    BallOperationRequest Index :=
  Sum.inr (Sum.inl ⟨r, s, PLift.up h, index⟩)

/-- Request the negation of a current point. -/
def neg (radius : ℚ≥0) (index : Index radius) :
    BallOperationRequest Index :=
  Sum.inr (Sum.inr (Sum.inl ⟨radius, index⟩))

/-- Request the sum of two current points in their exact output radius. -/
def add (r s : ℚ≥0) (left : Index r) (right : Index s) :
    BallOperationRequest Index :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨r, s, left, right⟩)))

/-- Request a rational scalar multiple in its exact output radius. -/
def smul (q : ℚ) (radius : ℚ≥0) (index : Index radius) :
    BallOperationRequest Index :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨q, radius, index⟩)))

/-- The radius sort in which a typed operation request produces its value. -/
def outputRadius : BallOperationRequest Index → ℚ≥0
  | .inl radius => radius
  | .inr (.inl request) => request.2.1
  | .inr (.inr (.inl request)) => request.1
  | .inr (.inr (.inr (.inl request))) => request.1 + request.2.1
  | .inr (.inr (.inr (.inr request))) => request.1.nnabs * request.2.1

variable {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}

/-- Evaluate one operation request in the ambient ball structure. -/
def value (request : BallOperationRequest Index)
    (M : BallStructure.{u, w} Symbol symbolRadius)
    (indexMap : ∀ radius, Index radius → M.Ball radius) :
    M.Ball request.outputRadius :=
  match request with
  | .inl radius => M.zero radius
  | .inr (.inl request) =>
      M.inclusion request.2.2.1.down
        (indexMap request.1 request.2.2.2)
  | .inr (.inr (.inl request)) =>
      M.neg request.1 (indexMap request.1 request.2)
  | .inr (.inr (.inr (.inl request))) =>
      M.add request.1 request.2.1
        (indexMap request.1 request.2.2.1,
          indexMap request.2.1 request.2.2.2)
  | .inr (.inr (.inr (.inr request))) =>
      M.smul request.1 request.2.1
        (indexMap request.2.1 request.2.2)

@[simp]
theorem outputRadius_zero (radius : ℚ≥0) :
    outputRadius (zero (Index := Index) radius) = radius :=
  rfl

@[simp]
theorem outputRadius_inclusion {r s : ℚ≥0} (h : r ≤ s)
    (index : Index r) :
    outputRadius (inclusion h index) = s :=
  rfl

@[simp]
theorem outputRadius_neg (radius : ℚ≥0) (index : Index radius) :
    outputRadius (neg radius index) = radius :=
  rfl

@[simp]
theorem outputRadius_add (r s : ℚ≥0) (left : Index r)
    (right : Index s) :
    outputRadius (add r s left right) = r + s :=
  rfl

@[simp]
theorem outputRadius_smul (q : ℚ) (radius : ℚ≥0)
    (index : Index radius) :
    outputRadius (smul q radius index) = q.nnabs * radius :=
  rfl

@[simp]
theorem value_zero (M : BallStructure.{u, w} Symbol symbolRadius)
    (indexMap : ∀ radius, Index radius → M.Ball radius)
    (radius : ℚ≥0) :
    value (zero (Index := Index) radius) M indexMap = M.zero radius :=
  rfl

@[simp]
theorem value_inclusion (M : BallStructure.{u, w} Symbol symbolRadius)
    (indexMap : ∀ radius, Index radius → M.Ball radius)
    {r s : ℚ≥0} (h : r ≤ s) (index : Index r) :
    value (inclusion h index) M indexMap =
      M.inclusion h (indexMap r index) :=
  rfl

@[simp]
theorem value_neg (M : BallStructure.{u, w} Symbol symbolRadius)
    (indexMap : ∀ radius, Index radius → M.Ball radius)
    (radius : ℚ≥0) (index : Index radius) :
    value (neg radius index) M indexMap =
      M.neg radius (indexMap radius index) :=
  rfl

@[simp]
theorem value_add (M : BallStructure.{u, w} Symbol symbolRadius)
    (indexMap : ∀ radius, Index radius → M.Ball radius)
    (r s : ℚ≥0) (left : Index r) (right : Index s) :
    value (add r s left right) M indexMap =
      M.add r s (indexMap r left, indexMap s right) :=
  rfl

@[simp]
theorem value_smul (M : BallStructure.{u, w} Symbol symbolRadius)
    (indexMap : ∀ radius, Index radius → M.Ball radius)
    (q : ℚ) (radius : ℚ≥0) (index : Index radius) :
    value (smul q radius index) M indexMap =
      M.smul q radius (indexMap radius index) :=
  rfl

end BallOperationRequest

/-- Operation requests whose value belongs to one specified output sort. -/
def BallOperationRequestsAt (Index : ℚ≥0 → Type v) (radius : ℚ≥0) :=
  {request : BallOperationRequest Index // request.outputRadius = radius}

noncomputable instance ballOperationRequestsAt_countable
    (Index : ℚ≥0 → Type v) [∀ radius, Countable (Index radius)]
    (radius : ℚ≥0) : Countable (BallOperationRequestsAt Index radius) := by
  unfold BallOperationRequestsAt
  infer_instance

end


end NormFormula.ContinuousLogic
