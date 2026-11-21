import NormFormula.ContinuousLogic.WitnessRequest

/-!
# Countable stages of approximate witness closure

A `WitnessIndexing` is a pair of countable index types mapped into the row and
parameter sorts of one ambient structure.  Its successor retains every old
index and adds one new index for every approximate quantifier-witness request
over the current stage.  The construction remains countable and can be
iterated through all finite stages.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u v w

/-- Countable row and parameter index types mapped into one ambient
many-predicate structure. -/
structure WitnessIndexing {Symbol : Type w}
    (M : MultiStructure.{u, v, w} Symbol) where
  RowIndex : Type (max u v w)
  ParameterIndex : Type (max u v w)
  rowCountable : Countable RowIndex
  parameterCountable : Countable ParameterIndex
  rowMap : RowIndex → M.Row
  parameterMap : ParameterIndex → M.Parameter

namespace WitnessIndexing

variable {Symbol : Type w} {M : MultiStructure.{u, v, w} Symbol}

/-- Bundle two countable ambient maps as a witness indexing. -/
def ofMaps {RowIndex ParameterIndex : Type (max u v w)}
    [Countable RowIndex] [Countable ParameterIndex]
    (rowMap : RowIndex → M.Row)
    (parameterMap : ParameterIndex → M.Parameter) : WitnessIndexing M where
  RowIndex := RowIndex
  ParameterIndex := ParameterIndex
  rowCountable := inferInstance
  parameterCountable := inferInstance
  rowMap := rowMap
  parameterMap := parameterMap

/-- Enlarge a countable indexing by every row and parameter witness request
over its current tuples. -/
noncomputable def next [Encodable Symbol]
    (current : WitnessIndexing M) : WitnessIndexing M where
  RowIndex := current.RowIndex ⊕
    RowWitnessRequest Symbol current.RowIndex current.ParameterIndex
  ParameterIndex := current.ParameterIndex ⊕
    ParameterWitnessRequest Symbol current.RowIndex current.ParameterIndex
  rowCountable := by
    letI := current.rowCountable
    letI := current.parameterCountable
    infer_instance
  parameterCountable := by
    letI := current.rowCountable
    letI := current.parameterCountable
    infer_instance
  rowMap
    | .inl index => current.rowMap index
    | .inr request =>
        request.witness M current.rowMap current.parameterMap
  parameterMap
    | .inl index => current.parameterMap index
    | .inr request =>
        request.witness M current.rowMap current.parameterMap

/-- Include an old row index into the successor stage. -/
def oldRow [Encodable Symbol] (current : WitnessIndexing M) :
    current.RowIndex → current.next.RowIndex :=
  Sum.inl

/-- Include an old parameter index into the successor stage. -/
def oldParameter [Encodable Symbol] (current : WitnessIndexing M) :
    current.ParameterIndex → current.next.ParameterIndex :=
  Sum.inl

/-- Include a row request as its new successor-stage index. -/
def requestedRow [Encodable Symbol] (current : WitnessIndexing M) :
    RowWitnessRequest Symbol current.RowIndex current.ParameterIndex →
      current.next.RowIndex :=
  Sum.inr

/-- Include a parameter request as its new successor-stage index. -/
def requestedParameter [Encodable Symbol] (current : WitnessIndexing M) :
    ParameterWitnessRequest Symbol current.RowIndex current.ParameterIndex →
      current.next.ParameterIndex :=
  Sum.inr

@[simp]
theorem next_rowMap_old [Encodable Symbol] (current : WitnessIndexing M)
    (index : current.RowIndex) :
    current.next.rowMap (current.oldRow index) = current.rowMap index :=
  rfl

@[simp]
theorem next_parameterMap_old [Encodable Symbol]
    (current : WitnessIndexing M) (index : current.ParameterIndex) :
    current.next.parameterMap (current.oldParameter index) =
      current.parameterMap index :=
  rfl

@[simp]
theorem next_rowMap_requested [Encodable Symbol]
    (current : WitnessIndexing M)
    (request : RowWitnessRequest Symbol current.RowIndex current.ParameterIndex) :
    current.next.rowMap (current.requestedRow request) =
      request.witness M current.rowMap current.parameterMap :=
  rfl

@[simp]
theorem next_parameterMap_requested [Encodable Symbol]
    (current : WitnessIndexing M)
    (request : ParameterWitnessRequest Symbol current.RowIndex
      current.ParameterIndex) :
    current.next.parameterMap (current.requestedParameter request) =
      request.witness M current.rowMap current.parameterMap :=
  rfl

/-- Iterate witness enlargement through all finite stages. -/
noncomputable def iterate [Encodable Symbol]
    (initial : WitnessIndexing M) : ℕ → WitnessIndexing M
  | 0 => initial
  | n + 1 => (iterate initial n).next

@[simp]
theorem iterate_zero [Encodable Symbol] (initial : WitnessIndexing M) :
    initial.iterate 0 = initial :=
  rfl

@[simp]
theorem iterate_succ [Encodable Symbol] (initial : WitnessIndexing M)
    (n : ℕ) :
    initial.iterate (n + 1) = (initial.iterate n).next :=
  rfl

/-- Include a row index from stage `n` into stage `n + 1`. -/
def iterateOldRow [Encodable Symbol] (initial : WitnessIndexing M)
    (n : ℕ) :
    (initial.iterate n).RowIndex → (initial.iterate (n + 1)).RowIndex :=
  (initial.iterate n).oldRow

/-- Include a parameter index from stage `n` into stage `n + 1`. -/
def iterateOldParameter [Encodable Symbol] (initial : WitnessIndexing M)
    (n : ℕ) :
    (initial.iterate n).ParameterIndex →
      (initial.iterate (n + 1)).ParameterIndex :=
  (initial.iterate n).oldParameter

@[simp]
theorem iterate_rowMap_old [Encodable Symbol] (initial : WitnessIndexing M)
    (n : ℕ) (index : (initial.iterate n).RowIndex) :
    (initial.iterate (n + 1)).rowMap (initial.iterateOldRow n index) =
      (initial.iterate n).rowMap index :=
  rfl

@[simp]
theorem iterate_parameterMap_old [Encodable Symbol]
    (initial : WitnessIndexing M) (n : ℕ)
    (index : (initial.iterate n).ParameterIndex) :
    (initial.iterate (n + 1)).parameterMap
        (initial.iterateOldParameter n index) =
      (initial.iterate n).parameterMap index :=
  rfl

end WitnessIndexing

end

end NormFormula.ContinuousLogic
