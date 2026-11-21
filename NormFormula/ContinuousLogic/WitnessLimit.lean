import NormFormula.ContinuousLogic.WitnessStage

/-!
# The countable limit of approximate witness stages

Stage inclusions are iterated to lift indices into every later stage while
preserving their ambient values.  The sigma types of indices over all finite
stages are countable.  Finally, every pair of finite row and parameter tuples
from these limit indices is lifted to one common stage, again without changing
any ambient value.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u v w

namespace WitnessIndexing

variable {Symbol : Type w} {M : MultiStructure.{u, v, w} Symbol}

/-- Lift a row index forward by a specified number of stages. -/
def liftRowBy [Encodable Symbol] (initial : WitnessIndexing M) (n : ℕ) :
    ∀ k : ℕ, (initial.iterate n).RowIndex →
      (initial.iterate (n + k)).RowIndex
  | 0, index => index
  | k + 1, index => initial.iterateOldRow (n + k)
      (liftRowBy initial n k index)

/-- Lift a parameter index forward by a specified number of stages. -/
def liftParameterBy [Encodable Symbol] (initial : WitnessIndexing M) (n : ℕ) :
    ∀ k : ℕ, (initial.iterate n).ParameterIndex →
      (initial.iterate (n + k)).ParameterIndex
  | 0, index => index
  | k + 1, index => initial.iterateOldParameter (n + k)
      (liftParameterBy initial n k index)

@[simp]
theorem rowMap_liftRowBy [Encodable Symbol] (initial : WitnessIndexing M)
    (n k : ℕ) (index : (initial.iterate n).RowIndex) :
    (initial.iterate (n + k)).rowMap (initial.liftRowBy n k index) =
      (initial.iterate n).rowMap index := by
  induction k with
  | zero => rfl
  | succ k induction =>
      calc
        (initial.iterate (n + (k + 1))).rowMap
            (initial.liftRowBy n (k + 1) index) =
            (initial.iterate (n + k)).rowMap
              (initial.liftRowBy n k index) := by
                simpa only [liftRowBy, Nat.add_assoc] using
                  initial.iterate_rowMap_old (n + k)
                    (initial.liftRowBy n k index)
        _ = (initial.iterate n).rowMap index := induction

@[simp]
theorem parameterMap_liftParameterBy [Encodable Symbol]
    (initial : WitnessIndexing M) (n k : ℕ)
    (index : (initial.iterate n).ParameterIndex) :
    (initial.iterate (n + k)).parameterMap
        (initial.liftParameterBy n k index) =
      (initial.iterate n).parameterMap index := by
  induction k with
  | zero => rfl
  | succ k induction =>
      calc
        (initial.iterate (n + (k + 1))).parameterMap
            (initial.liftParameterBy n (k + 1) index) =
            (initial.iterate (n + k)).parameterMap
              (initial.liftParameterBy n k index) := by
                simpa only [liftParameterBy, Nat.add_assoc] using
                  initial.iterate_parameterMap_old (n + k)
                    (initial.liftParameterBy n k index)
        _ = (initial.iterate n).parameterMap index := induction

/-- Lift a row index from stage `n` to an arbitrary later stage `m`. -/
def liftRowTo [Encodable Symbol] (initial : WitnessIndexing M)
    {n m : ℕ} (h : n ≤ m) (index : (initial.iterate n).RowIndex) :
    (initial.iterate m).RowIndex :=
  cast (congrArg (fun stage => (initial.iterate stage).RowIndex)
    (Nat.add_sub_of_le h))
    (initial.liftRowBy n (m - n) index)

/-- Lift a parameter index from stage `n` to an arbitrary later stage `m`. -/
def liftParameterTo [Encodable Symbol] (initial : WitnessIndexing M)
    {n m : ℕ} (h : n ≤ m)
    (index : (initial.iterate n).ParameterIndex) :
    (initial.iterate m).ParameterIndex :=
  cast (congrArg (fun stage => (initial.iterate stage).ParameterIndex)
    (Nat.add_sub_of_le h))
    (initial.liftParameterBy n (m - n) index)

theorem rowMap_cast_stage [Encodable Symbol] (initial : WitnessIndexing M)
    {n m : ℕ} (e : n = m) (index : (initial.iterate n).RowIndex) :
    (initial.iterate m).rowMap
        (cast (congrArg (fun stage => (initial.iterate stage).RowIndex) e)
          index) =
      (initial.iterate n).rowMap index := by
  subst m
  rfl

theorem parameterMap_cast_stage [Encodable Symbol]
    (initial : WitnessIndexing M) {n m : ℕ} (e : n = m)
    (index : (initial.iterate n).ParameterIndex) :
    (initial.iterate m).parameterMap
        (cast (congrArg (fun stage => (initial.iterate stage).ParameterIndex) e)
          index) =
      (initial.iterate n).parameterMap index := by
  subst m
  rfl

@[simp]
theorem rowMap_liftRowTo [Encodable Symbol] (initial : WitnessIndexing M)
    {n m : ℕ} (h : n ≤ m) (index : (initial.iterate n).RowIndex) :
    (initial.iterate m).rowMap (initial.liftRowTo h index) =
      (initial.iterate n).rowMap index := by
  unfold liftRowTo
  calc
    (initial.iterate m).rowMap
        (cast (congrArg (fun stage => (initial.iterate stage).RowIndex)
          (Nat.add_sub_of_le h))
          (initial.liftRowBy n (m - n) index)) =
        (initial.iterate (n + (m - n))).rowMap
          (initial.liftRowBy n (m - n) index) :=
      initial.rowMap_cast_stage (Nat.add_sub_of_le h)
        (initial.liftRowBy n (m - n) index)
    _ = (initial.iterate n).rowMap index :=
      initial.rowMap_liftRowBy n (m - n) index

@[simp]
theorem parameterMap_liftParameterTo [Encodable Symbol]
    (initial : WitnessIndexing M) {n m : ℕ} (h : n ≤ m)
    (index : (initial.iterate n).ParameterIndex) :
    (initial.iterate m).parameterMap (initial.liftParameterTo h index) =
      (initial.iterate n).parameterMap index := by
  unfold liftParameterTo
  calc
    (initial.iterate m).parameterMap
        (cast (congrArg (fun stage => (initial.iterate stage).ParameterIndex)
          (Nat.add_sub_of_le h))
          (initial.liftParameterBy n (m - n) index)) =
        (initial.iterate (n + (m - n))).parameterMap
          (initial.liftParameterBy n (m - n) index) :=
      initial.parameterMap_cast_stage (Nat.add_sub_of_le h)
        (initial.liftParameterBy n (m - n) index)
    _ = (initial.iterate n).parameterMap index :=
      initial.parameterMap_liftParameterBy n (m - n) index

/-- The countable sigma type of row indices over every finite stage. -/
def LimitRowIndex [Encodable Symbol] (initial : WitnessIndexing M) :=
  Σ n : ℕ, (initial.iterate n).RowIndex

/-- The countable sigma type of parameter indices over every finite stage. -/
def LimitParameterIndex [Encodable Symbol] (initial : WitnessIndexing M) :=
  Σ n : ℕ, (initial.iterate n).ParameterIndex

noncomputable instance [Encodable Symbol] (initial : WitnessIndexing M) :
    Countable initial.LimitRowIndex := by
  unfold LimitRowIndex
  letI : ∀ n, Countable (initial.iterate n).RowIndex :=
    fun n => (initial.iterate n).rowCountable
  infer_instance

noncomputable instance [Encodable Symbol] (initial : WitnessIndexing M) :
    Countable initial.LimitParameterIndex := by
  unfold LimitParameterIndex
  letI : ∀ n, Countable (initial.iterate n).ParameterIndex :=
    fun n => (initial.iterate n).parameterCountable
  infer_instance

/-- Map every limit row index to its ambient value. -/
def limitRowMap [Encodable Symbol] (initial : WitnessIndexing M) :
    initial.LimitRowIndex → M.Row :=
  fun index => (initial.iterate index.1).rowMap index.2

/-- Map every limit parameter index to its ambient value. -/
def limitParameterMap [Encodable Symbol] (initial : WitnessIndexing M) :
    initial.LimitParameterIndex → M.Parameter :=
  fun index => (initial.iterate index.1).parameterMap index.2

/-- The largest stage occurring in one finite tuple of sigma indices. -/
def commonStage {arity : ℕ} {Index : ℕ → Type*}
    (indices : Fin arity → Σ n, Index n) : ℕ :=
  Finset.univ.sup fun i => (indices i).1

theorem stage_le_commonStage {arity : ℕ} {Index : ℕ → Type*}
    (indices : Fin arity → Σ n, Index n) (i : Fin arity) :
    (indices i).1 ≤ commonStage indices :=
  Finset.le_sup (f := fun j => (indices j).1) (Finset.mem_univ i)

def limitRowsAtCommonStage [Encodable Symbol] (initial : WitnessIndexing M)
    {arity : ℕ} (indices : Fin arity → initial.LimitRowIndex) :
    Fin arity → (initial.iterate (commonStage indices)).RowIndex :=
  fun i => initial.liftRowTo (stage_le_commonStage indices i) (indices i).2

def limitParametersAtCommonStage [Encodable Symbol]
    (initial : WitnessIndexing M) {arity : ℕ}
    (indices : Fin arity → initial.LimitParameterIndex) :
    Fin arity → (initial.iterate (commonStage indices)).ParameterIndex :=
  fun i => initial.liftParameterTo (stage_le_commonStage indices i) (indices i).2

@[simp]
theorem rowMap_limitRowsAtCommonStage [Encodable Symbol]
    (initial : WitnessIndexing M) {arity : ℕ}
    (indices : Fin arity → initial.LimitRowIndex) (i : Fin arity) :
    (initial.iterate (commonStage indices)).rowMap
        (initial.limitRowsAtCommonStage indices i) =
      initial.limitRowMap (indices i) := by
  exact initial.rowMap_liftRowTo _ _

@[simp]
theorem parameterMap_limitParametersAtCommonStage [Encodable Symbol]
    (initial : WitnessIndexing M) {arity : ℕ}
    (indices : Fin arity → initial.LimitParameterIndex) (i : Fin arity) :
    (initial.iterate (commonStage indices)).parameterMap
        (initial.limitParametersAtCommonStage indices i) =
      initial.limitParameterMap (indices i) := by
  exact initial.parameterMap_liftParameterTo _ _

/-- One stage containing both a finite row tuple and a finite parameter
tuple. -/
def commonAssignmentStage [Encodable Symbol] (initial : WitnessIndexing M)
    {rowArity parameterArity : ℕ}
    (rows : Fin rowArity → initial.LimitRowIndex)
    (parameters : Fin parameterArity → initial.LimitParameterIndex) : ℕ :=
  max (commonStage rows) (commonStage parameters)

theorem row_stage_le_commonAssignmentStage [Encodable Symbol]
    (initial : WitnessIndexing M) {rowArity parameterArity : ℕ}
    (rows : Fin rowArity → initial.LimitRowIndex)
    (parameters : Fin parameterArity → initial.LimitParameterIndex)
    (i : Fin rowArity) :
    (rows i).1 ≤ initial.commonAssignmentStage rows parameters :=
  (stage_le_commonStage rows i).trans (le_max_left _ _)

theorem parameter_stage_le_commonAssignmentStage [Encodable Symbol]
    (initial : WitnessIndexing M) {rowArity parameterArity : ℕ}
    (rows : Fin rowArity → initial.LimitRowIndex)
    (parameters : Fin parameterArity → initial.LimitParameterIndex)
    (i : Fin parameterArity) :
    (parameters i).1 ≤ initial.commonAssignmentStage rows parameters :=
  (stage_le_commonStage parameters i).trans (le_max_right _ _)

/-- Lift a finite limit-row tuple into its common assignment stage. -/
def limitRowsAtAssignmentStage [Encodable Symbol]
    (initial : WitnessIndexing M) {rowArity parameterArity : ℕ}
    (rows : Fin rowArity → initial.LimitRowIndex)
    (parameters : Fin parameterArity → initial.LimitParameterIndex) :
    Fin rowArity →
      (initial.iterate (initial.commonAssignmentStage rows parameters)).RowIndex :=
  fun i => initial.liftRowTo
    (initial.row_stage_le_commonAssignmentStage rows parameters i) (rows i).2

/-- Lift a finite limit-parameter tuple into its common assignment stage. -/
def limitParametersAtAssignmentStage [Encodable Symbol]
    (initial : WitnessIndexing M) {rowArity parameterArity : ℕ}
    (rows : Fin rowArity → initial.LimitRowIndex)
    (parameters : Fin parameterArity → initial.LimitParameterIndex) :
    Fin parameterArity →
      (initial.iterate
        (initial.commonAssignmentStage rows parameters)).ParameterIndex :=
  fun i => initial.liftParameterTo
    (initial.parameter_stage_le_commonAssignmentStage rows parameters i)
    (parameters i).2

@[simp]
theorem rowMap_limitRowsAtAssignmentStage [Encodable Symbol]
    (initial : WitnessIndexing M) {rowArity parameterArity : ℕ}
    (rows : Fin rowArity → initial.LimitRowIndex)
    (parameters : Fin parameterArity → initial.LimitParameterIndex)
    (i : Fin rowArity) :
    (initial.iterate (initial.commonAssignmentStage rows parameters)).rowMap
        (initial.limitRowsAtAssignmentStage rows parameters i) =
      initial.limitRowMap (rows i) := by
  exact initial.rowMap_liftRowTo _ _

@[simp]
theorem parameterMap_limitParametersAtAssignmentStage [Encodable Symbol]
    (initial : WitnessIndexing M) {rowArity parameterArity : ℕ}
    (rows : Fin rowArity → initial.LimitRowIndex)
    (parameters : Fin parameterArity → initial.LimitParameterIndex)
    (i : Fin parameterArity) :
    (initial.iterate
      (initial.commonAssignmentStage rows parameters)).parameterMap
        (initial.limitParametersAtAssignmentStage rows parameters i) =
      initial.limitParameterMap (parameters i) := by
  exact initial.parameterMap_liftParameterTo _ _

end WitnessIndexing

end

end NormFormula.ContinuousLogic
