import NormFormula.ContinuousLogic.QuantifierWitness

/-!
# Countable approximate-witness requests

This file packages every request used at one stage of a continuous
Tarski--Vaught construction.  A request records a rational formula with one
distinguished quantified variable, finite tuples from the current row and
parameter index types, a precision, and whether a supremum or infimum witness
is required.

When the predicate alphabet and both index types are countable, the row and
parameter request types are countable.  Each request also chooses an ambient
witness and records its approximation inequality.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe w u v

/-- Whether an approximate witness approaches a supremum from below or an
infimum from above. -/
inductive QuantifierDirection where
  | supremum
  | infimum
  deriving Encodable, DecidableEq

/-- The positive error assigned to a natural-number precision request. -/
def witnessError (precision : ℕ) : ℝ :=
  1 / ((precision : ℝ) + 1)

theorem witnessError_pos (precision : ℕ) :
    0 < witnessError precision := by
  unfold witnessError
  positivity

/-- One request to adjoin an approximate row witness. -/
structure RowWitnessRequest (Symbol : Type w)
    (RowIndex : Type u) (ParameterIndex : Type v) where
  rowVars : ℕ
  parameterVars : ℕ
  formula : CountableFormula Symbol (rowVars + 1) parameterVars
  rows : Fin rowVars → RowIndex
  parameters : Fin parameterVars → ParameterIndex
  precision : ℕ
  direction : QuantifierDirection

/-- One request to adjoin an approximate parameter witness. -/
structure ParameterWitnessRequest (Symbol : Type w)
    (RowIndex : Type u) (ParameterIndex : Type v) where
  rowVars : ℕ
  parameterVars : ℕ
  formula : CountableFormula Symbol rowVars (parameterVars + 1)
  rows : Fin rowVars → RowIndex
  parameters : Fin parameterVars → ParameterIndex
  precision : ℕ
  direction : QuantifierDirection

/-- A sigma-product code exposing countability of row-witness requests. -/
def RowWitnessRequestCode (Symbol : Type w)
    (RowIndex : Type u) (ParameterIndex : Type v) :=
  Σ rowVars : ℕ, Σ parameterVars : ℕ,
    CountableFormula Symbol (rowVars + 1) parameterVars ×
      (Fin rowVars → RowIndex) ×
      (Fin parameterVars → ParameterIndex) ×
      ℕ × QuantifierDirection

/-- Row-witness requests are equivalent to their explicit countable
sigma-product code. -/
def rowWitnessRequestEquiv :
    RowWitnessRequest Symbol RowIndex ParameterIndex ≃
      RowWitnessRequestCode Symbol RowIndex ParameterIndex where
  toFun request := ⟨request.rowVars, request.parameterVars,
    request.formula, request.rows, request.parameters,
    request.precision, request.direction⟩
  invFun code := ⟨code.1, code.2.1, code.2.2.1, code.2.2.2.1,
    code.2.2.2.2.1, code.2.2.2.2.2.1, code.2.2.2.2.2.2⟩
  left_inv request := by cases request; rfl
  right_inv code := by
    rcases code with ⟨rowVars, parameterVars, formula, rows, parameters,
      precision, direction⟩
    rfl

noncomputable instance [Encodable Symbol] [Countable RowIndex]
    [Countable ParameterIndex] :
    Countable (RowWitnessRequestCode Symbol RowIndex ParameterIndex) := by
  unfold RowWitnessRequestCode
  infer_instance

noncomputable instance [Encodable Symbol] [Countable RowIndex]
    [Countable ParameterIndex] :
    Countable (RowWitnessRequest Symbol RowIndex ParameterIndex) :=
  Countable.of_equiv (RowWitnessRequestCode Symbol RowIndex ParameterIndex)
    rowWitnessRequestEquiv.symm

/-- A sigma-product code exposing countability of parameter-witness
requests. -/
def ParameterWitnessRequestCode (Symbol : Type w)
    (RowIndex : Type u) (ParameterIndex : Type v) :=
  Σ rowVars : ℕ, Σ parameterVars : ℕ,
    CountableFormula Symbol rowVars (parameterVars + 1) ×
      (Fin rowVars → RowIndex) ×
      (Fin parameterVars → ParameterIndex) ×
      ℕ × QuantifierDirection

/-- Parameter-witness requests are equivalent to their explicit countable
sigma-product code. -/
def parameterWitnessRequestEquiv :
    ParameterWitnessRequest Symbol RowIndex ParameterIndex ≃
      ParameterWitnessRequestCode Symbol RowIndex ParameterIndex where
  toFun request := ⟨request.rowVars, request.parameterVars,
    request.formula, request.rows, request.parameters,
    request.precision, request.direction⟩
  invFun code := ⟨code.1, code.2.1, code.2.2.1, code.2.2.2.1,
    code.2.2.2.2.1, code.2.2.2.2.2.1, code.2.2.2.2.2.2⟩
  left_inv request := by cases request; rfl
  right_inv code := by
    rcases code with ⟨rowVars, parameterVars, formula, rows, parameters,
      precision, direction⟩
    rfl

noncomputable instance [Encodable Symbol] [Countable RowIndex]
    [Countable ParameterIndex] :
    Countable (ParameterWitnessRequestCode Symbol RowIndex ParameterIndex) := by
  unfold ParameterWitnessRequestCode
  infer_instance

noncomputable instance [Encodable Symbol] [Countable RowIndex]
    [Countable ParameterIndex] :
    Countable (ParameterWitnessRequest Symbol RowIndex ParameterIndex) :=
  Countable.of_equiv (ParameterWitnessRequestCode Symbol RowIndex ParameterIndex)
    parameterWitnessRequestEquiv.symm

namespace RowWitnessRequest

variable {Symbol : Type w} {RowIndex : Type u} {ParameterIndex : Type v}

/-- Interpret a request's row tuple in an ambient structure. -/
def ambientRows (request : RowWitnessRequest Symbol RowIndex ParameterIndex)
    {M : MultiStructure Symbol} (rowMap : RowIndex → M.Row) :
    Fin request.rowVars → M.Row :=
  fun i => rowMap (request.rows i)

/-- Interpret a request's parameter tuple in an ambient structure. -/
def ambientParameters
    (request : RowWitnessRequest Symbol RowIndex ParameterIndex)
    {M : MultiStructure Symbol} (parameterMap : ParameterIndex → M.Parameter) :
    Fin request.parameterVars → M.Parameter :=
  fun i => parameterMap (request.parameters i)

/-- Choose the ambient approximate row witness demanded by a request. -/
noncomputable def witness
    (request : RowWitnessRequest Symbol RowIndex ParameterIndex)
    (M : MultiStructure Symbol)
    (rowMap : RowIndex → M.Row)
    (parameterMap : ParameterIndex → M.Parameter) : M.Row :=
  match request.direction with
  | .supremum => Classical.choose
      (request.formula.toMultiFormula.exists_row_iSup_approximation M
        (request.ambientRows rowMap) (request.ambientParameters parameterMap)
        (witnessError_pos request.precision))
  | .infimum => Classical.choose
      (request.formula.toMultiFormula.exists_row_iInf_approximation M
        (request.ambientRows rowMap) (request.ambientParameters parameterMap)
        (witnessError_pos request.precision))

/-- The chosen row satisfies the directional approximation inequality encoded
by its request. -/
theorem witness_spec
    (request : RowWitnessRequest Symbol RowIndex ParameterIndex)
    (M : MultiStructure Symbol)
    (rowMap : RowIndex → M.Row)
    (parameterMap : ParameterIndex → M.Parameter) :
    match request.direction with
    | .supremum =>
        (((MultiFormula.iSupRow request.formula.toMultiFormula).realize M
            (request.ambientRows rowMap)
            (request.ambientParameters parameterMap) : ℝ) <
          (request.formula.toMultiFormula.realize M
            (Fin.cons (request.witness M rowMap parameterMap)
              (request.ambientRows rowMap))
            (request.ambientParameters parameterMap) : ℝ) +
              witnessError request.precision)
    | .infimum =>
        ((request.formula.toMultiFormula.realize M
            (Fin.cons (request.witness M rowMap parameterMap)
              (request.ambientRows rowMap))
            (request.ambientParameters parameterMap) : ℝ) <
          ((MultiFormula.iInfRow request.formula.toMultiFormula).realize M
            (request.ambientRows rowMap)
            (request.ambientParameters parameterMap) : ℝ) +
              witnessError request.precision) := by
  cases hdirection : request.direction with
  | supremum =>
      simpa only [hdirection, witness] using Classical.choose_spec
        (request.formula.toMultiFormula.exists_row_iSup_approximation M
          (request.ambientRows rowMap) (request.ambientParameters parameterMap)
          (witnessError_pos request.precision))
  | infimum =>
      simpa only [hdirection, witness] using Classical.choose_spec
        (request.formula.toMultiFormula.exists_row_iInf_approximation M
          (request.ambientRows rowMap) (request.ambientParameters parameterMap)
          (witnessError_pos request.precision))

end RowWitnessRequest

namespace ParameterWitnessRequest

variable {Symbol : Type w} {RowIndex : Type u} {ParameterIndex : Type v}

/-- Interpret a request's row tuple in an ambient structure. -/
def ambientRows
    (request : ParameterWitnessRequest Symbol RowIndex ParameterIndex)
    {M : MultiStructure Symbol} (rowMap : RowIndex → M.Row) :
    Fin request.rowVars → M.Row :=
  fun i => rowMap (request.rows i)

/-- Interpret a request's parameter tuple in an ambient structure. -/
def ambientParameters
    (request : ParameterWitnessRequest Symbol RowIndex ParameterIndex)
    {M : MultiStructure Symbol} (parameterMap : ParameterIndex → M.Parameter) :
    Fin request.parameterVars → M.Parameter :=
  fun i => parameterMap (request.parameters i)

/-- Choose the ambient approximate parameter witness demanded by a request. -/
noncomputable def witness
    (request : ParameterWitnessRequest Symbol RowIndex ParameterIndex)
    (M : MultiStructure Symbol)
    (rowMap : RowIndex → M.Row)
    (parameterMap : ParameterIndex → M.Parameter) : M.Parameter :=
  match request.direction with
  | .supremum => Classical.choose
      (request.formula.toMultiFormula.exists_parameter_iSup_approximation M
        (request.ambientRows rowMap) (request.ambientParameters parameterMap)
        (witnessError_pos request.precision))
  | .infimum => Classical.choose
      (request.formula.toMultiFormula.exists_parameter_iInf_approximation M
        (request.ambientRows rowMap) (request.ambientParameters parameterMap)
        (witnessError_pos request.precision))

/-- The chosen parameter satisfies the directional approximation inequality
encoded by its request. -/
theorem witness_spec
    (request : ParameterWitnessRequest Symbol RowIndex ParameterIndex)
    (M : MultiStructure Symbol)
    (rowMap : RowIndex → M.Row)
    (parameterMap : ParameterIndex → M.Parameter) :
    match request.direction with
    | .supremum =>
        (((MultiFormula.iSupParameter request.formula.toMultiFormula).realize M
            (request.ambientRows rowMap)
            (request.ambientParameters parameterMap) : ℝ) <
          (request.formula.toMultiFormula.realize M
            (request.ambientRows rowMap)
            (Fin.cons (request.witness M rowMap parameterMap)
              (request.ambientParameters parameterMap)) : ℝ) +
              witnessError request.precision)
    | .infimum =>
        ((request.formula.toMultiFormula.realize M
            (request.ambientRows rowMap)
            (Fin.cons (request.witness M rowMap parameterMap)
              (request.ambientParameters parameterMap)) : ℝ) <
          ((MultiFormula.iInfParameter request.formula.toMultiFormula).realize M
            (request.ambientRows rowMap)
            (request.ambientParameters parameterMap) : ℝ) +
              witnessError request.precision) := by
  cases hdirection : request.direction with
  | supremum =>
      simpa only [hdirection, witness] using Classical.choose_spec
        (request.formula.toMultiFormula.exists_parameter_iSup_approximation M
          (request.ambientRows rowMap) (request.ambientParameters parameterMap)
          (witnessError_pos request.precision))
  | infimum =>
      simpa only [hdirection, witness] using Classical.choose_spec
        (request.formula.toMultiFormula.exists_parameter_iInf_approximation M
          (request.ambientRows rowMap) (request.ambientParameters parameterMap)
          (witnessError_pos request.precision))

end ParameterWitnessRequest

end

end NormFormula.ContinuousLogic
