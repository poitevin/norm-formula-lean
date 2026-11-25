import NormFormula.ContinuousLogic.BanachBallOperationRequest

/-!
# Sortwise stages of approximate witness closure

A `BallWitnessIndexing` assigns a countable index type to every rational ball
sort and maps those indices into one ambient ball structure.  Its successor
retains all old indices and, in each radius, adjoins both the approximate
quantifier requests and the typed algebraic-operation requests whose recorded
output radius is that sort.  The construction stays countable sort by sort
and iterates through all finite stages.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u w

/-- A countable dependent family of indices mapped into the corresponding
sorts of one ambient rational-ball structure. -/
structure BallWitnessIndexing {Symbol : Type w}
    {symbolRadius : Symbol → ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius) where
  Index : ℚ≥0 → Type (max u w)
  indexCountable : ∀ radius, Countable (Index radius)
  indexMap : ∀ radius, Index radius → M.Ball radius

namespace BallWitnessIndexing

variable {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
  {M : BallStructure.{u, w} Symbol symbolRadius}


/-- Requests over the current stage whose witness belongs to one specified
radius sort. -/
def RequestsAt (current : BallWitnessIndexing M) (radius : ℚ≥0) :=
  {request : BallWitnessRequest Symbol symbolRadius current.Index //
    request.quantifiedRadius = radius}

noncomputable instance requestsAt_countable [Encodable Symbol]
    (current : BallWitnessIndexing M) (radius : ℚ≥0) :
    Countable (current.RequestsAt radius) := by
  letI : ∀ r, Countable (current.Index r) := current.indexCountable
  unfold RequestsAt
  infer_instance

/-- Enlarge every radius sort by all current approximate witness and typed
algebraic-operation requests targeting that sort. -/
noncomputable def next [Encodable Symbol]
    (current : BallWitnessIndexing M) : BallWitnessIndexing M where
  Index := fun radius ↦ current.Index radius ⊕
    (current.RequestsAt radius ⊕
      BallOperationRequestsAt current.Index radius)
  indexCountable := fun radius ↦ by
    letI : Countable (current.Index radius) := current.indexCountable radius
    letI : ∀ r, Countable (current.Index r) := current.indexCountable
    infer_instance
  indexMap := fun radius index ↦
    match index with
    | .inl old => current.indexMap radius old
    | .inr (.inl request) => by
        rw [← request.2]
        exact request.1.witness M current.indexMap
    | .inr (.inr request) => by
        rw [← request.2]
        exact request.1.value M current.indexMap

/-- Include an old point of a radius sort into the successor stage. -/
def old [Encodable Symbol] (current : BallWitnessIndexing M)
    (radius : ℚ≥0) : current.Index radius → current.next.Index radius :=
  Sum.inl

/-- Include a request as the new successor-stage index in its own quantified
radius sort. -/
def requested [Encodable Symbol] (current : BallWitnessIndexing M)
    (request : BallWitnessRequest Symbol symbolRadius current.Index) :
    current.next.Index request.quantifiedRadius :=
  Sum.inr (Sum.inl ⟨request, rfl⟩)

/-- Include a typed algebraic request as the new successor-stage index in
its computed output radius sort. -/
def operated [Encodable Symbol] (current : BallWitnessIndexing M)
    (request : BallOperationRequest current.Index) :
    current.next.Index request.outputRadius :=
  Sum.inr (Sum.inr ⟨request, rfl⟩)


/-- Iterate sortwise witness adjunction through all finite stages. -/
noncomputable def iterate [Encodable Symbol]
    (initial : BallWitnessIndexing M) : ℕ → BallWitnessIndexing M
  | 0 => initial
  | n + 1 => (initial.iterate n).next


/-- Lift one index from a stage to its immediate successor. -/
def oldAtStage [Encodable Symbol] (initial : BallWitnessIndexing M)
    (stage : ℕ) (radius : ℚ≥0) :
    (initial.iterate stage).Index radius →
      (initial.iterate (stage + 1)).Index radius :=
  (initial.iterate stage).old radius

@[simp]
theorem indexMap_oldAtStage [Encodable Symbol]
    (initial : BallWitnessIndexing M) (stage : ℕ) (radius : ℚ≥0)
    (index : (initial.iterate stage).Index radius) :
    (initial.iterate (stage + 1)).indexMap radius
        (initial.oldAtStage stage radius index) =
      (initial.iterate stage).indexMap radius index :=
  rfl

/-- Lift one index through a specified number of successor stages. -/
def liftBy [Encodable Symbol] (initial : BallWitnessIndexing M)
    (stage steps : ℕ) (radius : ℚ≥0) :
    (initial.iterate stage).Index radius →
      (initial.iterate (stage + steps)).Index radius :=
  match steps with
  | 0 => id
  | steps + 1 => fun index ↦
      initial.oldAtStage (stage + steps) radius
        (initial.liftBy stage steps radius index)

@[simp]
theorem indexMap_liftBy [Encodable Symbol]
    (initial : BallWitnessIndexing M)
    (stage steps : ℕ) (radius : ℚ≥0)
    (index : (initial.iterate stage).Index radius) :
    (initial.iterate (stage + steps)).indexMap radius
        (initial.liftBy stage steps radius index) =
      (initial.iterate stage).indexMap radius index := by
  induction steps with
  | zero => rfl
  | succ steps induction =>
      change (initial.iterate (stage + steps + 1)).indexMap radius
          (initial.oldAtStage (stage + steps) radius
            (initial.liftBy stage steps radius index)) = _
      rw [indexMap_oldAtStage, induction]

end BallWitnessIndexing

end

end NormFormula.ContinuousLogic
