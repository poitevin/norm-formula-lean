import NormFormula.ContinuousLogic.WitnessLimit

/-!
# Quantifier witnesses inside the countable stage limit

A finite assignment from the limit indices is lifted to its common stage.
The corresponding rational quantifier request is placed in the successor
stage, hence determines another limit index.  Its ambient value satisfies the
requested supremum or infimum approximation inequality for the original limit
assignment.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u v w

namespace WitnessIndexing

variable {Symbol : Type w} {M : MultiStructure.{u, v, w} Symbol}

/-- The common-stage row request associated to a finite limit assignment. -/
def limitRowRequest [Encodable Symbol] (initial : WitnessIndexing M)
    {rowVars parameterVars : ℕ}
    (formula : CountableFormula Symbol (rowVars + 1) parameterVars)
    (rows : Fin rowVars → initial.LimitRowIndex)
    (parameters : Fin parameterVars → initial.LimitParameterIndex)
    (precision : ℕ) (direction : QuantifierDirection) :
    RowWitnessRequest Symbol
      (initial.iterate (initial.commonAssignmentStage rows parameters)).RowIndex
      (initial.iterate
        (initial.commonAssignmentStage rows parameters)).ParameterIndex where
  rowVars := rowVars
  parameterVars := parameterVars
  formula := formula
  rows := initial.limitRowsAtAssignmentStage rows parameters
  parameters := initial.limitParametersAtAssignmentStage rows parameters
  precision := precision
  direction := direction

/-- The common-stage parameter request associated to a finite limit
assignment. -/
def limitParameterRequest [Encodable Symbol] (initial : WitnessIndexing M)
    {rowVars parameterVars : ℕ}
    (formula : CountableFormula Symbol rowVars (parameterVars + 1))
    (rows : Fin rowVars → initial.LimitRowIndex)
    (parameters : Fin parameterVars → initial.LimitParameterIndex)
    (precision : ℕ) (direction : QuantifierDirection) :
    ParameterWitnessRequest Symbol
      (initial.iterate (initial.commonAssignmentStage rows parameters)).RowIndex
      (initial.iterate
        (initial.commonAssignmentStage rows parameters)).ParameterIndex where
  rowVars := rowVars
  parameterVars := parameterVars
  formula := formula
  rows := initial.limitRowsAtAssignmentStage rows parameters
  parameters := initial.limitParametersAtAssignmentStage rows parameters
  precision := precision
  direction := direction

/-- The successor-stage limit row index selected for a rational quantifier
request. -/
def limitRowWitness [Encodable Symbol] (initial : WitnessIndexing M)
    {rowVars parameterVars : ℕ}
    (formula : CountableFormula Symbol (rowVars + 1) parameterVars)
    (rows : Fin rowVars → initial.LimitRowIndex)
    (parameters : Fin parameterVars → initial.LimitParameterIndex)
    (precision : ℕ) (direction : QuantifierDirection) :
    initial.LimitRowIndex :=
  ⟨initial.commonAssignmentStage rows parameters + 1,
    (initial.iterate (initial.commonAssignmentStage rows parameters)).requestedRow
      (initial.limitRowRequest formula rows parameters precision direction)⟩

/-- The successor-stage limit parameter index selected for a rational
quantifier request. -/
def limitParameterWitness [Encodable Symbol] (initial : WitnessIndexing M)
    {rowVars parameterVars : ℕ}
    (formula : CountableFormula Symbol rowVars (parameterVars + 1))
    (rows : Fin rowVars → initial.LimitRowIndex)
    (parameters : Fin parameterVars → initial.LimitParameterIndex)
    (precision : ℕ) (direction : QuantifierDirection) :
    initial.LimitParameterIndex :=
  ⟨initial.commonAssignmentStage rows parameters + 1,
    (initial.iterate
      (initial.commonAssignmentStage rows parameters)).requestedParameter
      (initial.limitParameterRequest formula rows parameters precision direction)⟩

@[simp]
theorem limitRowMap_limitRowWitness [Encodable Symbol]
    (initial : WitnessIndexing M) {rowVars parameterVars : ℕ}
    (formula : CountableFormula Symbol (rowVars + 1) parameterVars)
    (rows : Fin rowVars → initial.LimitRowIndex)
    (parameters : Fin parameterVars → initial.LimitParameterIndex)
    (precision : ℕ) (direction : QuantifierDirection) :
    initial.limitRowMap
        (initial.limitRowWitness formula rows parameters precision direction) =
      (initial.limitRowRequest formula rows parameters precision direction).witness
        M
        (initial.iterate
          (initial.commonAssignmentStage rows parameters)).rowMap
        (initial.iterate
          (initial.commonAssignmentStage rows parameters)).parameterMap :=
  rfl

@[simp]
theorem limitParameterMap_limitParameterWitness [Encodable Symbol]
    (initial : WitnessIndexing M) {rowVars parameterVars : ℕ}
    (formula : CountableFormula Symbol rowVars (parameterVars + 1))
    (rows : Fin rowVars → initial.LimitRowIndex)
    (parameters : Fin parameterVars → initial.LimitParameterIndex)
    (precision : ℕ) (direction : QuantifierDirection) :
    initial.limitParameterMap
        (initial.limitParameterWitness formula rows parameters precision direction) =
      (initial.limitParameterRequest formula rows parameters precision direction).witness
        M
        (initial.iterate
          (initial.commonAssignmentStage rows parameters)).rowMap
        (initial.iterate
          (initial.commonAssignmentStage rows parameters)).parameterMap :=
  rfl

/-- Every rational row-quantifier request over a limit assignment has a
verified witness whose index belongs to the limit. -/
theorem limitRowWitness_spec [Encodable Symbol]
    (initial : WitnessIndexing M) {rowVars parameterVars : ℕ}
    (formula : CountableFormula Symbol (rowVars + 1) parameterVars)
    (rows : Fin rowVars → initial.LimitRowIndex)
    (parameters : Fin parameterVars → initial.LimitParameterIndex)
    (precision : ℕ) (direction : QuantifierDirection) :
    match direction with
    | .supremum =>
        (((MultiFormula.iSupRow formula.toMultiFormula).realize M
            (fun i => initial.limitRowMap (rows i))
            (fun i => initial.limitParameterMap (parameters i)) : ℝ) <
          (formula.toMultiFormula.realize M
            (Fin.cons
              (initial.limitRowMap
                (initial.limitRowWitness formula rows parameters precision direction))
              (fun i => initial.limitRowMap (rows i)))
            (fun i => initial.limitParameterMap (parameters i)) : ℝ) +
              witnessError precision)
    | .infimum =>
        ((formula.toMultiFormula.realize M
            (Fin.cons
              (initial.limitRowMap
                (initial.limitRowWitness formula rows parameters precision direction))
              (fun i => initial.limitRowMap (rows i)))
            (fun i => initial.limitParameterMap (parameters i)) : ℝ) <
          ((MultiFormula.iInfRow formula.toMultiFormula).realize M
            (fun i => initial.limitRowMap (rows i))
            (fun i => initial.limitParameterMap (parameters i)) : ℝ) +
              witnessError precision) := by
  have hspec :=
    (initial.limitRowRequest formula rows parameters precision direction).witness_spec
      M
      (initial.iterate
        (initial.commonAssignmentStage rows parameters)).rowMap
      (initial.iterate
        (initial.commonAssignmentStage rows parameters)).parameterMap
  have hrows :
      (initial.limitRowRequest formula rows parameters precision direction).ambientRows
          (initial.iterate
            (initial.commonAssignmentStage rows parameters)).rowMap =
        (fun i => initial.limitRowMap (rows i)) := by
    funext i
    exact initial.rowMap_limitRowsAtAssignmentStage rows parameters i
  have hparameters :
      (initial.limitRowRequest formula rows parameters precision direction).ambientParameters
          (initial.iterate
            (initial.commonAssignmentStage rows parameters)).parameterMap =
        (fun i => initial.limitParameterMap (parameters i)) := by
    funext i
    exact initial.parameterMap_limitParametersAtAssignmentStage rows parameters i
  rw [hrows, hparameters] at hspec
  simpa using hspec

/-- Every rational parameter-quantifier request over a limit assignment has a
verified witness whose index belongs to the limit. -/
theorem limitParameterWitness_spec [Encodable Symbol]
    (initial : WitnessIndexing M) {rowVars parameterVars : ℕ}
    (formula : CountableFormula Symbol rowVars (parameterVars + 1))
    (rows : Fin rowVars → initial.LimitRowIndex)
    (parameters : Fin parameterVars → initial.LimitParameterIndex)
    (precision : ℕ) (direction : QuantifierDirection) :
    match direction with
    | .supremum =>
        (((MultiFormula.iSupParameter formula.toMultiFormula).realize M
            (fun i => initial.limitRowMap (rows i))
            (fun i => initial.limitParameterMap (parameters i)) : ℝ) <
          (formula.toMultiFormula.realize M
            (fun i => initial.limitRowMap (rows i))
            (Fin.cons
              (initial.limitParameterMap
                (initial.limitParameterWitness formula rows parameters
                  precision direction))
              (fun i => initial.limitParameterMap (parameters i))) : ℝ) +
              witnessError precision)
    | .infimum =>
        ((formula.toMultiFormula.realize M
            (fun i => initial.limitRowMap (rows i))
            (Fin.cons
              (initial.limitParameterMap
                (initial.limitParameterWitness formula rows parameters
                  precision direction))
              (fun i => initial.limitParameterMap (parameters i))) : ℝ) <
          ((MultiFormula.iInfParameter formula.toMultiFormula).realize M
            (fun i => initial.limitRowMap (rows i))
            (fun i => initial.limitParameterMap (parameters i)) : ℝ) +
              witnessError precision) := by
  have hspec :=
    (initial.limitParameterRequest formula rows parameters precision direction).witness_spec
      M
      (initial.iterate
        (initial.commonAssignmentStage rows parameters)).rowMap
      (initial.iterate
        (initial.commonAssignmentStage rows parameters)).parameterMap
  have hrows :
      (initial.limitParameterRequest formula rows parameters precision direction).ambientRows
          (initial.iterate
            (initial.commonAssignmentStage rows parameters)).rowMap =
        (fun i => initial.limitRowMap (rows i)) := by
    funext i
    exact initial.rowMap_limitRowsAtAssignmentStage rows parameters i
  have hparameters :
      (initial.limitParameterRequest formula rows parameters precision direction).ambientParameters
          (initial.iterate
            (initial.commonAssignmentStage rows parameters)).parameterMap =
        (fun i => initial.limitParameterMap (parameters i)) := by
    funext i
    exact initial.parameterMap_limitParametersAtAssignmentStage rows parameters i
  rw [hrows, hparameters] at hspec
  simpa using hspec

end WitnessIndexing

end

end NormFormula.ContinuousLogic
