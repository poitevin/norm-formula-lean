import NormFormula.ContinuousLogic.BanachBallWitnessStage

/-!
# The countable limit of rational-ball witness stages

The sortwise stage inclusions lift indices to every later stage without
changing their ambient values.  Taking a sigma type over all finite stages
therefore gives one countable limit-index type for every rational radius.
Every finite dependent assignment from these limit types can be lifted to a
single common stage, again preserving all ambient values.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u w

namespace BallWitnessIndexing

variable {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
  {M : BallStructure.{u, w} Symbol symbolRadius}

/-- Lift an index from stage `n` to an arbitrary later stage `m`. -/
def liftTo [Encodable Symbol] (initial : BallWitnessIndexing M)
    {n m : ℕ} (h : n ≤ m) (radius : ℚ≥0)
    (index : (initial.iterate n).Index radius) :
    (initial.iterate m).Index radius :=
  cast (congrArg (fun stage ↦ (initial.iterate stage).Index radius)
    (Nat.add_sub_of_le h))
    (initial.liftBy n (m - n) radius index)

/-- Casting a stage-indexed point along equality of stages preserves its
ambient value. -/
theorem indexMap_cast_stage [Encodable Symbol]
    (initial : BallWitnessIndexing M) {n m : ℕ} (e : n = m)
    (radius : ℚ≥0) (index : (initial.iterate n).Index radius) :
    (initial.iterate m).indexMap radius
        (cast (congrArg (fun stage ↦ (initial.iterate stage).Index radius) e)
          index) =
      (initial.iterate n).indexMap radius index := by
  subst m
  rfl

@[simp]
theorem indexMap_liftTo [Encodable Symbol]
    (initial : BallWitnessIndexing M) {n m : ℕ} (h : n ≤ m)
    (radius : ℚ≥0) (index : (initial.iterate n).Index radius) :
    (initial.iterate m).indexMap radius
        (initial.liftTo h radius index) =
      (initial.iterate n).indexMap radius index := by
  unfold liftTo
  calc
    (initial.iterate m).indexMap radius
        (cast (congrArg
          (fun stage ↦ (initial.iterate stage).Index radius)
          (Nat.add_sub_of_le h))
          (initial.liftBy n (m - n) radius index)) =
      (initial.iterate (n + (m - n))).indexMap radius
        (initial.liftBy n (m - n) radius index) :=
      initial.indexMap_cast_stage (Nat.add_sub_of_le h) radius
        (initial.liftBy n (m - n) radius index)
    _ = (initial.iterate n).indexMap radius index :=
      initial.indexMap_liftBy n (m - n) radius index

/-- The sigma type of indices in one radius sort over every finite stage. -/
def LimitIndex [Encodable Symbol] (initial : BallWitnessIndexing M)
    (radius : ℚ≥0) :=
  Σ stage : ℕ, (initial.iterate stage).Index radius

noncomputable instance limitIndex_countable [Encodable Symbol]
    (initial : BallWitnessIndexing M) (radius : ℚ≥0) :
    Countable (initial.LimitIndex radius) := by
  unfold LimitIndex
  letI : ∀ stage, Countable ((initial.iterate stage).Index radius) :=
    fun stage ↦ (initial.iterate stage).indexCountable radius
  infer_instance

/-- Interpret a limit index by its value at the stage where it originated. -/
def limitMap [Encodable Symbol] (initial : BallWitnessIndexing M)
    (radius : ℚ≥0) : initial.LimitIndex radius → M.Ball radius :=
  fun index ↦ (initial.iterate index.1).indexMap radius index.2

/-- The largest stage occurring in a finite dependent typed assignment. -/
def commonStage [Encodable Symbol] (initial : BallWitnessIndexing M)
    {n : ℕ} {context : BallContext n}
    (indices : ∀ i : Fin n, initial.LimitIndex (context i)) : ℕ :=
  Finset.univ.sup fun i ↦ (indices i).1

/-- Every component of a finite limit assignment originates no later than
its common stage. -/
theorem stage_le_commonStage [Encodable Symbol]
    (initial : BallWitnessIndexing M)
    {n : ℕ} {context : BallContext n}
    (indices : ∀ i : Fin n, initial.LimitIndex (context i)) (i : Fin n) :
    (indices i).1 ≤ initial.commonStage indices :=
  Finset.le_sup (f := fun j ↦ (indices j).1) (Finset.mem_univ i)

/-- Lift every component of a finite dependent limit assignment into its one
common finite stage. -/
def limitAssignmentAtCommonStage [Encodable Symbol]
    (initial : BallWitnessIndexing M)
    {n : ℕ} {context : BallContext n}
    (indices : ∀ i : Fin n, initial.LimitIndex (context i)) :
    ∀ i : Fin n,
      (initial.iterate (initial.commonStage indices)).Index (context i) :=
  fun i ↦ initial.liftTo (initial.stage_le_commonStage indices i)
    (context i) (indices i).2

/-- Common-stage lifting preserves the ambient value of every component. -/
@[simp]
theorem indexMap_limitAssignmentAtCommonStage [Encodable Symbol]
    (initial : BallWitnessIndexing M)
    {n : ℕ} {context : BallContext n}
    (indices : ∀ i : Fin n, initial.LimitIndex (context i)) (i : Fin n) :
    (initial.iterate (initial.commonStage indices)).indexMap (context i)
        (initial.limitAssignmentAtCommonStage indices i) =
      initial.limitMap (context i) (indices i) := by
  exact initial.indexMap_liftTo _ _ _

/-- Interpret a finite dependent limit assignment in the ambient ball
structure. -/
def ambientLimitAssignment [Encodable Symbol]
    (initial : BallWitnessIndexing M)
    {n : ℕ} {context : BallContext n}
    (indices : ∀ i : Fin n, initial.LimitIndex (context i)) :
    BallTerm.Assignment M.toRationalBallSystem context :=
  fun i ↦ initial.limitMap (context i) (indices i)


end BallWitnessIndexing

end

end NormFormula.ContinuousLogic
