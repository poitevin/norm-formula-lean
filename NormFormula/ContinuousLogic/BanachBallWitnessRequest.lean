import NormFormula.ContinuousLogic.BanachBallFormulaDensity
import NormFormula.ContinuousLogic.WitnessRequest

/-!
# Countable approximate-witness requests for rational ball sorts

A ball-sorted quantifier request remembers the quantified radius, the finite
context of the remaining free variables, a rational typed formula in the
extended context, a tuple of current indices with the prescribed dependent
sorts, a precision, and a supremum/infimum direction.

For a countable family of current indices and an encodable predicate
alphabet, the total request type is countable.  Every request chooses an
ambient witness in exactly its quantified ball and records the corresponding
approximation inequality.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u v w

namespace BallFormula

/-- A point in the quantified ball approximates a typed supremum from below
at every positive tolerance. -/
theorem exists_iSup_approximation
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n} (radius : ℚ≥0)
    (formula : BallFormula Symbol symbolRadius (Fin.cons radius context))
    (M : BallStructure.{u, w} Symbol symbolRadius)
    (assignment : BallTerm.Assignment M.toRationalBallSystem context)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : M.Ball radius,
      (((BallFormula.iSup radius formula).realize M assignment : ℝ) <
        (formula.realize M (Fin.cons x assignment) : ℝ) + ε) :=
  NormFormula.ContinuousLogic.exists_iSup_approximation _ hε

/-- A point in the quantified ball approximates a typed infimum from above
at every positive tolerance. -/
theorem exists_iInf_approximation
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n} (radius : ℚ≥0)
    (formula : BallFormula Symbol symbolRadius (Fin.cons radius context))
    (M : BallStructure.{u, w} Symbol symbolRadius)
    (assignment : BallTerm.Assignment M.toRationalBallSystem context)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : M.Ball radius,
      ((formula.realize M (Fin.cons x assignment) : ℝ) <
        ((BallFormula.iInf radius formula).realize M assignment : ℝ) + ε) :=
  NormFormula.ContinuousLogic.exists_iInf_approximation _ hε

end BallFormula

/-- One approximate quantifier-witness request over a dependent family of
current ball indices. -/
structure BallWitnessRequest (Symbol : Type w)
    (symbolRadius : Symbol → ℚ≥0) (Index : ℚ≥0 → Type v) where
  variableCount : ℕ
  context : BallContext variableCount
  quantifiedRadius : ℚ≥0
  formula : CountableBallFormula Symbol symbolRadius
    (Fin.cons quantifiedRadius context)
  indices : ∀ i : Fin variableCount, Index (context i)
  precision : ℕ
  direction : QuantifierDirection

/-- An explicit sigma-product code exposing countability of ball-witness
requests. -/
def BallWitnessRequestCode (Symbol : Type w)
    (symbolRadius : Symbol → ℚ≥0) (Index : ℚ≥0 → Type v) :=
  Σ variableCount : ℕ, Σ context : BallContext variableCount,
    Σ quantifiedRadius : ℚ≥0,
      CountableBallFormula Symbol symbolRadius
          (Fin.cons quantifiedRadius context) ×
        (∀ i : Fin variableCount, Index (context i)) ×
        ℕ × QuantifierDirection

/-- Ball-witness requests are equivalent to their countable sigma-product
codes. -/
def ballWitnessRequestEquiv
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {Index : ℚ≥0 → Type v} :
    BallWitnessRequest Symbol symbolRadius Index ≃
      BallWitnessRequestCode Symbol symbolRadius Index where
  toFun request := ⟨request.variableCount, request.context,
    request.quantifiedRadius, request.formula, request.indices,
    request.precision, request.direction⟩
  invFun code := ⟨code.1, code.2.1, code.2.2.1, code.2.2.2.1,
    code.2.2.2.2.1, code.2.2.2.2.2.1, code.2.2.2.2.2.2⟩
  left_inv request := by cases request; rfl
  right_inv code := by
    rcases code with ⟨variableCount, context, radius, formula, indices,
      precision, direction⟩
    rfl

noncomputable instance ballWitnessRequestCode_countable
    {Symbol : Type w} [Encodable Symbol]
    (symbolRadius : Symbol → ℚ≥0) (Index : ℚ≥0 → Type v)
    [∀ radius, Countable (Index radius)] :
    Countable (BallWitnessRequestCode Symbol symbolRadius Index) := by
  unfold BallWitnessRequestCode
  infer_instance

noncomputable instance ballWitnessRequest_countable
    {Symbol : Type w} [Encodable Symbol]
    (symbolRadius : Symbol → ℚ≥0) (Index : ℚ≥0 → Type v)
    [∀ radius, Countable (Index radius)] :
    Countable (BallWitnessRequest Symbol symbolRadius Index) :=
  Countable.of_equiv (BallWitnessRequestCode Symbol symbolRadius Index)
    ballWitnessRequestEquiv.symm

namespace BallWitnessRequest

variable {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
  {Index : ℚ≥0 → Type v}

/-- Interpret a request's dependent tuple in an ambient ball structure. -/
def ambientAssignment
    (request : BallWitnessRequest Symbol symbolRadius Index)
    {M : BallStructure.{u, w} Symbol symbolRadius}
    (indexMap : ∀ radius, Index radius → M.Ball radius) :
    BallTerm.Assignment M.toRationalBallSystem request.context :=
  fun i ↦ indexMap (request.context i) (request.indices i)

/-- Choose the ambient approximate witness demanded by a ball-sorted
request. -/
noncomputable def witness
    (request : BallWitnessRequest Symbol symbolRadius Index)
    (M : BallStructure.{u, w} Symbol symbolRadius)
    (indexMap : ∀ radius, Index radius → M.Ball radius) :
    M.Ball request.quantifiedRadius :=
  match request.direction with
  | .supremum => Classical.choose
      (request.formula.toBallFormula.exists_iSup_approximation
        request.quantifiedRadius M (request.ambientAssignment indexMap)
        (witnessError_pos request.precision))
  | .infimum => Classical.choose
      (request.formula.toBallFormula.exists_iInf_approximation
        request.quantifiedRadius M (request.ambientAssignment indexMap)
        (witnessError_pos request.precision))

/-- The chosen witness lies in the requested radius sort and satisfies the
encoded directional approximation inequality. -/
theorem witness_spec
    (request : BallWitnessRequest Symbol symbolRadius Index)
    (M : BallStructure.{u, w} Symbol symbolRadius)
    (indexMap : ∀ radius, Index radius → M.Ball radius) :
    match request.direction with
    | .supremum =>
        (((BallFormula.iSup request.quantifiedRadius
            request.formula.toBallFormula).realize M
              (request.ambientAssignment indexMap) : ℝ) <
          (request.formula.toBallFormula.realize M
            (Fin.cons (request.witness M indexMap)
              (request.ambientAssignment indexMap)) : ℝ) +
            witnessError request.precision)
    | .infimum =>
        ((request.formula.toBallFormula.realize M
            (Fin.cons (request.witness M indexMap)
              (request.ambientAssignment indexMap)) : ℝ) <
          ((BallFormula.iInf request.quantifiedRadius
            request.formula.toBallFormula).realize M
              (request.ambientAssignment indexMap) : ℝ) +
            witnessError request.precision) := by
  cases hdirection : request.direction with
  | supremum =>
      simpa only [hdirection, witness] using Classical.choose_spec
        (request.formula.toBallFormula.exists_iSup_approximation
          request.quantifiedRadius M (request.ambientAssignment indexMap)
          (witnessError_pos request.precision))
  | infimum =>
      simpa only [hdirection, witness] using Classical.choose_spec
        (request.formula.toBallFormula.exists_iInf_approximation
          request.quantifiedRadius M (request.ambientAssignment indexMap)
          (witnessError_pos request.precision))

end BallWitnessRequest

end

end NormFormula.ContinuousLogic
