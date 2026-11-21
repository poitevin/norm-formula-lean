import NormFormula.ContinuousLogic.BanachBallNormAddReduct

/-!
# Mixed-radius norm reducts of predicate-free Banach ball structures

This file generalizes the fixed-radius reduct adapter to independently chosen
row and parameter radii.  Its syntax translation keeps an arbitrary typed
context together with explicit placements of row and parameter variables and
proofs of their respective radii.  This permits row and parameter quantifiers
to be interleaved without identifying the two sorts.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u v

/-- A typed variable whose context entry is propositionally the requested
radius. -/
def BallTerm.variableAtRadius {n : ℕ} {context : BallContext n}
    (radius : ℚ≥0) (i : Fin n) (h : context i = radius) :
    BallTerm context radius :=
  BallTerm.castRadius h (.variable i)

/-- Read an assignment entry at a propositionally identified radius. -/
def BallTerm.assignmentValueAtRadius
    (S : RationalBallSystem.{u}) {n : ℕ} {context : BallContext n}
    (radius : ℚ≥0)
    (assignment : BallTerm.Assignment S context)
    (i : Fin n) (h : context i = radius) : S.Ball radius :=
  h ▸ assignment i

@[simp]
theorem BallTerm.variableAtRadius_realize
    (S : RationalBallSystem.{u}) {n : ℕ} {context : BallContext n}
    (radius : ℚ≥0) (i : Fin n) (h : context i = radius)
    (assignment : BallTerm.Assignment S context) :
    (BallTerm.variableAtRadius radius i h).realize S assignment =
      BallTerm.assignmentValueAtRadius S radius assignment i h := by
  simp only [BallTerm.variableAtRadius,
    BallTerm.assignmentValueAtRadius, BallTerm.realize_castRadius,
    BallTerm.realize_variable]

/-- Extend a placement of typed variables after prepending a newly bound
variable to the ball context. -/
def prependBallIndex {m n : ℕ} (index : Fin m → Fin n) :
    Fin (m + 1) → Fin (n + 1) :=
  Fin.cons (0 : Fin (n + 1)) (fun i ↦ (index i).succ)

/-- Shift a placement past a newly bound variable of the other sort. -/
def shiftBallIndex {m n : ℕ} (index : Fin m → Fin n) :
    Fin m → Fin (n + 1) :=
  fun i ↦ (index i).succ

theorem prependBallIndex_radius
    {m n : ℕ} (radius : ℚ≥0) (context : BallContext n)
    (index : Fin m → Fin n) (radiusAt : ∀ i, context (index i) = radius) :
    ∀ i, (Fin.cons radius context : BallContext (n + 1))
      (prependBallIndex index i) = radius := by
  intro i
  exact Fin.cases rfl (fun k ↦ radiusAt k) i

theorem shiftBallIndex_radius
    {m n : ℕ} (headRadius radius : ℚ≥0) (context : BallContext n)
    (index : Fin m → Fin n) (radiusAt : ∀ i, context (index i) = radius) :
    ∀ i, (Fin.cons headRadius context : BallContext (n + 1))
      (shiftBallIndex index i) = radius := by
  intro i
  exact radiusAt i

/-- The two-sorted norm reduct determined by independently typed row and
parameter balls. -/
def ballNormAddMixedMultiStructure
    (M : BallStructure.{u, 0} EmptyBallPredicate emptyBallPredicateRadius)
    (rowRadius parameterRadius : ℚ≥0) : MultiStructure NormAddSymbol where
  Row := M.Ball rowRadius
  Parameter := M.Ball parameterRadius
  rowNonempty := M.ballNonempty rowRadius
  parameterNonempty := M.ballNonempty parameterRadius
  predicate
    | .norm => fun x y ↦
        (predicateFreeNormAddFormula rowRadius parameterRadius).realize M
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))
  predicate_uniformContinuous := by
    intro symbol
    cases symbol
    have hassignment : UniformContinuous
        (fun p : M.Ball rowRadius × M.Ball parameterRadius ↦
          (Fin.cons p.1 (Fin.cons p.2 (fun i : Fin 0 ↦ nomatch i)) :
            BallTerm.Assignment M.toRationalBallSystem
              (![rowRadius, parameterRadius] : BallContext 2))) := by
      apply uniformContinuous_pi.mpr
      intro i
      fin_cases i
      · exact uniformContinuous_fst
      · exact uniformContinuous_snd
    exact ((predicateFreeNormAddFormula rowRadius parameterRadius).realize_uniformContinuous
      M).comp hassignment

@[simp]
theorem ballNormAddMixedMultiStructure_predicate
    (M : BallStructure.{u, 0} EmptyBallPredicate emptyBallPredicateRadius)
    (rowRadius parameterRadius : ℚ≥0)
    (x : M.Ball rowRadius) (y : M.Ball parameterRadius) :
    (ballNormAddMixedMultiStructure M rowRadius parameterRadius).predicate
        .norm x y =
      (predicateFreeNormAddFormula rowRadius parameterRadius).realize M
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) :=
  rfl

/-- Translate the full two-sorted norm syntax into a typed ball context whose
row and parameter variables may have different radii. -/
def MultiFormula.toMixedNormAddBallFormulaAux
    (rowRadius parameterRadius : ℚ≥0)
    {rowVars parameterVars n : ℕ} (context : BallContext n)
    (rowIndex : Fin rowVars → Fin n)
    (parameterIndex : Fin parameterVars → Fin n)
    (rowRadiusAt : ∀ i, context (rowIndex i) = rowRadius)
    (parameterRadiusAt : ∀ j, context (parameterIndex j) = parameterRadius) :
    MultiFormula NormAddSymbol rowVars parameterVars →
      BallFormula EmptyBallPredicate emptyBallPredicateRadius context
  | .predicate .norm i j =>
      .distance
        (.add
          (BallTerm.variableAtRadius rowRadius (rowIndex i) (rowRadiusAt i))
          (BallTerm.variableAtRadius parameterRadius (parameterIndex j)
            (parameterRadiusAt j)))
        (.zero (rowRadius + parameterRadius))
  | .constant value => .constant value
  | .connective gate formulas =>
      .connective gate fun i ↦
        (formulas i).toMixedNormAddBallFormulaAux
          rowRadius parameterRadius context rowIndex parameterIndex
          rowRadiusAt parameterRadiusAt
  | .iSupRow formula => by
      apply BallFormula.iSup rowRadius
      exact formula.toMixedNormAddBallFormulaAux
        rowRadius parameterRadius (Fin.cons rowRadius context)
        (Fin.cons 0 fun i ↦ (rowIndex i).succ)
        (fun j ↦ (parameterIndex j).succ)
        (fun i ↦ Fin.cases rfl (fun k ↦ rowRadiusAt k) i)
        (fun j ↦ parameterRadiusAt j)
  | .iInfRow formula => by
      apply BallFormula.iInf rowRadius
      exact formula.toMixedNormAddBallFormulaAux
        rowRadius parameterRadius (Fin.cons rowRadius context)
        (Fin.cons 0 fun i ↦ (rowIndex i).succ)
        (fun j ↦ (parameterIndex j).succ)
        (fun i ↦ Fin.cases rfl (fun k ↦ rowRadiusAt k) i)
        (fun j ↦ parameterRadiusAt j)
  | .iSupParameter formula => by
      apply BallFormula.iSup parameterRadius
      exact formula.toMixedNormAddBallFormulaAux
        rowRadius parameterRadius (Fin.cons parameterRadius context)
        (fun i ↦ (rowIndex i).succ)
        (Fin.cons 0 fun j ↦ (parameterIndex j).succ)
        (fun i ↦ rowRadiusAt i)
        (fun j ↦ Fin.cases rfl (fun k ↦ parameterRadiusAt k) j)
  | .iInfParameter formula => by
      apply BallFormula.iInf parameterRadius
      exact formula.toMixedNormAddBallFormulaAux
        rowRadius parameterRadius (Fin.cons parameterRadius context)
        (fun i ↦ (rowIndex i).succ)
        (Fin.cons 0 fun j ↦ (parameterIndex j).succ)
        (fun i ↦ rowRadiusAt i)
        (fun j ↦ Fin.cases rfl (fun k ↦ parameterRadiusAt k) j)

/-- The mixed-radius translation preserves realization in every
predicate-free ball structure. -/
theorem MultiFormula.realize_toMixedNormAddBallFormulaAux
    (M : BallStructure.{u, 0} EmptyBallPredicate emptyBallPredicateRadius)
    (rowRadius parameterRadius : ℚ≥0)
    {rowVars parameterVars n : ℕ} (context : BallContext n)
    (rowIndex : Fin rowVars → Fin n)
    (parameterIndex : Fin parameterVars → Fin n)
    (rowRadiusAt : ∀ i, context (rowIndex i) = rowRadius)
    (parameterRadiusAt : ∀ j, context (parameterIndex j) = parameterRadius)
    (formula : MultiFormula NormAddSymbol rowVars parameterVars)
    (assignment : BallTerm.Assignment M.toRationalBallSystem context) :
    (formula.toMixedNormAddBallFormulaAux rowRadius parameterRadius
        context rowIndex parameterIndex rowRadiusAt parameterRadiusAt).realize
        M assignment =
      formula.realize
        (ballNormAddMixedMultiStructure M rowRadius parameterRadius)
        (fun i ↦ BallTerm.assignmentValueAtRadius M.toRationalBallSystem
          rowRadius assignment (rowIndex i) (rowRadiusAt i))
        (fun j ↦ BallTerm.assignmentValueAtRadius M.toRationalBallSystem
          parameterRadius assignment (parameterIndex j) (parameterRadiusAt j)) := by
  induction formula generalizing n context with
  | predicate symbol i j =>
      cases symbol
      simp only [toMixedNormAddBallFormulaAux,
        BallTerm.variableAtRadius_realize, MultiFormula.realize,
        ballNormAddMixedMultiStructure_predicate,
        predicateFreeNormAddFormula, BallFormula.realize_distance,
        BallTerm.binaryAddTerm, BallTerm.realize, Fin.cons_zero]
      have hsnd :
          (Fin.cons
              (BallTerm.assignmentValueAtRadius M.toRationalBallSystem
                rowRadius assignment (rowIndex i) (rowRadiusAt i))
              (Fin.cons
                (BallTerm.assignmentValueAtRadius M.toRationalBallSystem
                  parameterRadius assignment (parameterIndex j)
                  (parameterRadiusAt j))
                (fun k : Fin 0 ↦ nomatch k)) :
            BallTerm.Assignment M.toRationalBallSystem
              (![rowRadius, parameterRadius] : BallContext 2)) (1 : Fin 2) =
            BallTerm.assignmentValueAtRadius M.toRationalBallSystem
              parameterRadius assignment (parameterIndex j)
              (parameterRadiusAt j) := by
        rfl
      rw [hsnd]
  | constant value =>
      rfl
  | connective gate formulas induction =>
      simp only [toMixedNormAddBallFormulaAux, BallFormula.realize,
        MultiFormula.realize]
      congr 1
      funext i
      exact induction i context rowIndex parameterIndex rowRadiusAt
        parameterRadiusAt assignment
  | iSupRow formula induction =>
      simp only [toMixedNormAddBallFormulaAux, BallFormula.realize,
        MultiFormula.realize]
      apply iSup_congr
      intro x
      let extendedRowIndex := prependBallIndex rowIndex
      let extendedParameterIndex := shiftBallIndex parameterIndex
      let extendedRowRadiusAt : ∀ i,
          (Fin.cons rowRadius context : BallContext (n + 1))
            (extendedRowIndex i) = rowRadius :=
        prependBallIndex_radius rowRadius context rowIndex rowRadiusAt
      let extendedParameterRadiusAt : ∀ j,
          (Fin.cons rowRadius context : BallContext (n + 1))
            (extendedParameterIndex j) =
            parameterRadius :=
        shiftBallIndex_radius rowRadius parameterRadius context parameterIndex
          parameterRadiusAt
      have hih := induction (Fin.cons rowRadius context)
        extendedRowIndex extendedParameterIndex
        extendedRowRadiusAt extendedParameterRadiusAt
        (Fin.cons x assignment)
      have hrows :
          (fun i ↦ BallTerm.assignmentValueAtRadius M.toRationalBallSystem
            rowRadius (Fin.cons x assignment) (extendedRowIndex i)
            (extendedRowRadiusAt i)) =
          Fin.cons x (fun i ↦ BallTerm.assignmentValueAtRadius
            M.toRationalBallSystem rowRadius assignment (rowIndex i)
            (rowRadiusAt i)) := by
        funext i
        exact Fin.cases rfl (fun _ ↦ rfl) i
      have hparameters :
          (fun j ↦ BallTerm.assignmentValueAtRadius M.toRationalBallSystem
            parameterRadius (Fin.cons x assignment)
            (extendedParameterIndex j) (extendedParameterRadiusAt j)) =
          (fun j ↦ BallTerm.assignmentValueAtRadius M.toRationalBallSystem
            parameterRadius assignment (parameterIndex j)
            (parameterRadiusAt j)) := by
        funext j
        rfl
      rw [hrows, hparameters] at hih
      exact hih
  | iInfRow formula induction =>
      simp only [toMixedNormAddBallFormulaAux, BallFormula.realize,
        MultiFormula.realize]
      apply iInf_congr
      intro x
      let extendedRowIndex := prependBallIndex rowIndex
      let extendedParameterIndex := shiftBallIndex parameterIndex
      let extendedRowRadiusAt : ∀ i,
          (Fin.cons rowRadius context : BallContext (n + 1))
            (extendedRowIndex i) = rowRadius :=
        prependBallIndex_radius rowRadius context rowIndex rowRadiusAt
      let extendedParameterRadiusAt : ∀ j,
          (Fin.cons rowRadius context : BallContext (n + 1))
            (extendedParameterIndex j) =
            parameterRadius :=
        shiftBallIndex_radius rowRadius parameterRadius context parameterIndex
          parameterRadiusAt
      have hih := induction (Fin.cons rowRadius context)
        extendedRowIndex extendedParameterIndex
        extendedRowRadiusAt extendedParameterRadiusAt
        (Fin.cons x assignment)
      have hrows :
          (fun i ↦ BallTerm.assignmentValueAtRadius M.toRationalBallSystem
            rowRadius (Fin.cons x assignment) (extendedRowIndex i)
            (extendedRowRadiusAt i)) =
          Fin.cons x (fun i ↦ BallTerm.assignmentValueAtRadius
            M.toRationalBallSystem rowRadius assignment (rowIndex i)
            (rowRadiusAt i)) := by
        funext i
        exact Fin.cases rfl (fun _ ↦ rfl) i
      have hparameters :
          (fun j ↦ BallTerm.assignmentValueAtRadius M.toRationalBallSystem
            parameterRadius (Fin.cons x assignment)
            (extendedParameterIndex j) (extendedParameterRadiusAt j)) =
          (fun j ↦ BallTerm.assignmentValueAtRadius M.toRationalBallSystem
            parameterRadius assignment (parameterIndex j)
            (parameterRadiusAt j)) := by
        funext j
        rfl
      rw [hrows, hparameters] at hih
      exact hih
  | iSupParameter formula induction =>
      simp only [toMixedNormAddBallFormulaAux, BallFormula.realize,
        MultiFormula.realize]
      apply iSup_congr
      intro y
      let extendedRowIndex := shiftBallIndex rowIndex
      let extendedParameterIndex := prependBallIndex parameterIndex
      let extendedRowRadiusAt : ∀ i,
          (Fin.cons parameterRadius context : BallContext (n + 1))
            (extendedRowIndex i) = rowRadius :=
        shiftBallIndex_radius parameterRadius rowRadius context rowIndex
          rowRadiusAt
      let extendedParameterRadiusAt : ∀ j,
          (Fin.cons parameterRadius context : BallContext (n + 1))
            (extendedParameterIndex j) =
            parameterRadius :=
        prependBallIndex_radius parameterRadius context parameterIndex
          parameterRadiusAt
      have hih := induction (Fin.cons parameterRadius context)
        extendedRowIndex extendedParameterIndex
        extendedRowRadiusAt extendedParameterRadiusAt
        (Fin.cons y assignment)
      have hrows :
          (fun i ↦ BallTerm.assignmentValueAtRadius M.toRationalBallSystem
            rowRadius (Fin.cons y assignment) (extendedRowIndex i)
            (extendedRowRadiusAt i)) =
          (fun i ↦ BallTerm.assignmentValueAtRadius M.toRationalBallSystem
            rowRadius assignment (rowIndex i) (rowRadiusAt i)) := by
        funext i
        rfl
      have hparameters :
          (fun j ↦ BallTerm.assignmentValueAtRadius M.toRationalBallSystem
            parameterRadius (Fin.cons y assignment)
            (extendedParameterIndex j) (extendedParameterRadiusAt j)) =
          Fin.cons y (fun j ↦ BallTerm.assignmentValueAtRadius
            M.toRationalBallSystem parameterRadius assignment
            (parameterIndex j) (parameterRadiusAt j)) := by
        funext j
        exact Fin.cases rfl (fun _ ↦ rfl) j
      rw [hrows, hparameters] at hih
      exact hih
  | iInfParameter formula induction =>
      simp only [toMixedNormAddBallFormulaAux, BallFormula.realize,
        MultiFormula.realize]
      apply iInf_congr
      intro y
      let extendedRowIndex := shiftBallIndex rowIndex
      let extendedParameterIndex := prependBallIndex parameterIndex
      let extendedRowRadiusAt : ∀ i,
          (Fin.cons parameterRadius context : BallContext (n + 1))
            (extendedRowIndex i) = rowRadius :=
        shiftBallIndex_radius parameterRadius rowRadius context rowIndex
          rowRadiusAt
      let extendedParameterRadiusAt : ∀ j,
          (Fin.cons parameterRadius context : BallContext (n + 1))
            (extendedParameterIndex j) =
            parameterRadius :=
        prependBallIndex_radius parameterRadius context parameterIndex
          parameterRadiusAt
      have hih := induction (Fin.cons parameterRadius context)
        extendedRowIndex extendedParameterIndex
        extendedRowRadiusAt extendedParameterRadiusAt
        (Fin.cons y assignment)
      have hrows :
          (fun i ↦ BallTerm.assignmentValueAtRadius M.toRationalBallSystem
            rowRadius (Fin.cons y assignment) (extendedRowIndex i)
            (extendedRowRadiusAt i)) =
          (fun i ↦ BallTerm.assignmentValueAtRadius M.toRationalBallSystem
            rowRadius assignment (rowIndex i) (rowRadiusAt i)) := by
        funext i
        rfl
      have hparameters :
          (fun j ↦ BallTerm.assignmentValueAtRadius M.toRationalBallSystem
            parameterRadius (Fin.cons y assignment)
            (extendedParameterIndex j) (extendedParameterRadiusAt j)) =
          Fin.cons y (fun j ↦ BallTerm.assignmentValueAtRadius
            M.toRationalBallSystem parameterRadius assignment
            (parameterIndex j) (parameterRadiusAt j)) := by
        funext j
        exact Fin.cases rfl (fun _ ↦ rfl) j
      rw [hrows, hparameters] at hih
      exact hih

/-- The sentence-level mixed-radius translation starts from the empty typed
context. -/
def MultiSentence.toMixedNormAddBallSentence
    (rowRadius parameterRadius : ℚ≥0)
    (sentence : MultiSentence NormAddSymbol) :
    BallSentence EmptyBallPredicate emptyBallPredicateRadius :=
  sentence.toMixedNormAddBallFormulaAux rowRadius parameterRadius
    (Fin.elim0 : BallContext 0)
    (fun i : Fin 0 ↦ nomatch i)
    (fun j : Fin 0 ↦ nomatch j)
    (fun i : Fin 0 ↦ nomatch i)
    (fun j : Fin 0 ↦ nomatch j)

/-- Sentence values are preserved by the mixed-radius syntax translation. -/
theorem MultiSentence.value_toMixedNormAddBallFormula
    (M : BallStructure.{u, 0} EmptyBallPredicate emptyBallPredicateRadius)
    (rowRadius parameterRadius : ℚ≥0)
    (sentence : MultiSentence NormAddSymbol) :
    BallSentence.value
        (sentence.toMixedNormAddBallSentence rowRadius parameterRadius) M =
      sentence.value
        (ballNormAddMixedMultiStructure M rowRadius parameterRadius) := by
  unfold MultiSentence.toMixedNormAddBallSentence BallSentence.value
    MultiSentence.value
  have h := sentence.realize_toMixedNormAddBallFormulaAux M
    rowRadius parameterRadius
    (Fin.elim0 : BallContext 0)
    (fun i : Fin 0 ↦ nomatch i)
    (fun j : Fin 0 ↦ nomatch j)
    (fun i : Fin 0 ↦ nomatch i)
    (fun j : Fin 0 ↦ nomatch j)
    (fun k : Fin 0 ↦ nomatch k)
  have hRows :
      (fun i : Fin 0 ↦ BallTerm.assignmentValueAtRadius
        M.toRationalBallSystem rowRadius
        ((fun k : Fin 0 ↦ nomatch k) :
          BallTerm.Assignment M.toRationalBallSystem
            (Fin.elim0 : BallContext 0))
        (nomatch i) (by exact nomatch i)) =
        (Fin.elim0 : Fin 0 →
          (ballNormAddMixedMultiStructure M rowRadius parameterRadius).Row) :=
    Subsingleton.elim _ _
  have hParameters :
      (fun j : Fin 0 ↦ BallTerm.assignmentValueAtRadius
        M.toRationalBallSystem parameterRadius
        ((fun k : Fin 0 ↦ nomatch k) :
          BallTerm.Assignment M.toRationalBallSystem
            (Fin.elim0 : BallContext 0))
        (nomatch j) (by exact nomatch j)) =
        (Fin.elim0 : Fin 0 →
          (ballNormAddMixedMultiStructure M rowRadius parameterRadius).Parameter) :=
    Subsingleton.elim _ _
  rw [hRows, hParameters] at h
  exact h

/-- Same complete typed ball theory implies the same complete theory for
every associated mixed-radius norm reduct. -/
theorem ballSameCompleteTheory_mixedNormAddMultiStructure
    (M : BallStructure.{u, 0} EmptyBallPredicate emptyBallPredicateRadius)
    (N : BallStructure.{v, 0} EmptyBallPredicate emptyBallPredicateRadius)
    (rowRadius parameterRadius : ℚ≥0)
    (hTheory : BallSameCompleteTheory M N) :
    MultiSameCompleteTheory
      (ballNormAddMixedMultiStructure M rowRadius parameterRadius)
      (ballNormAddMixedMultiStructure N rowRadius parameterRadius) := by
  intro sentence
  rw [← MultiSentence.value_toMixedNormAddBallFormula,
    ← MultiSentence.value_toMixedNormAddBallFormula]
  exact hTheory
    (sentence.toMixedNormAddBallSentence rowRadius parameterRadius)

/-- The distinguished atom of the mixed-radius reduct has exactly the typed
norm-addition value. -/
@[simp]
theorem normAddMultiFormula_ballNormAddMixedMultiStructure_value
    (M : BallStructure.{u, 0} EmptyBallPredicate emptyBallPredicateRadius)
    (rowRadius parameterRadius : ℚ≥0)
    (x : M.Ball rowRadius) (y : M.Ball parameterRadius) :
    normAddMultiFormula.binaryValue
        (ballNormAddMixedMultiStructure M rowRadius parameterRadius) x y =
      (predicateFreeNormAddFormula rowRadius parameterRadius).binaryValue
        M x y :=
  rfl

/-- A typed mixed-radius infinite norm-addition witness is the same witness
in the associated two-sorted reduct. -/
theorem hasInfiniteIPWitness_mixedNormAddMultiStructure_iff
    (M : BallStructure.{u, 0} EmptyBallPredicate emptyBallPredicateRadius)
    (rowRadius parameterRadius : ℚ≥0) (low high : ℝ) :
    (predicateFreeNormAddFormula rowRadius parameterRadius).HasInfiniteIPWitness
        M low high ↔
      MultiFormula.HasInfiniteIPWitness
        (ballNormAddMixedMultiStructure M rowRadius parameterRadius)
        normAddMultiFormula low high :=
  Iff.rfl

/-- Complete-theory IP in the full ball language descends to complete-theory
IP of the associated mixed-radius norm reduct. -/
theorem hasIPInMixedNormAddMultiTheory_of_hasIPInBallTheory
    (M : BallStructure.{u, 0} EmptyBallPredicate emptyBallPredicateRadius)
    (rowRadius parameterRadius : ℚ≥0)
    (hIP : (predicateFreeNormAddFormula rowRadius parameterRadius).HasIPInCompleteTheory M) :
    MultiFormula.HasIPInCompleteTheory
      (ballNormAddMixedMultiStructure M rowRadius parameterRadius)
      normAddMultiFormula := by
  obtain ⟨N, hTheory, low, high, hgap, hWitness⟩ := hIP
  refine ⟨ballNormAddMixedMultiStructure N rowRadius parameterRadius,
    ballSameCompleteTheory_mixedNormAddMultiStructure M N
      rowRadius parameterRadius hTheory,
    low, high, hgap, ?_⟩
  exact (hasInfiniteIPWitness_mixedNormAddMultiStructure_iff
    N rowRadius parameterRadius low high).mp hWitness

/-- Bounded-local NIP of ambient norm addition proves complete-theory NIP
for every independently bounded row and parameter ball reduct. -/
theorem normAddMultiFormula_isNIPInCompleteTheory_ballNormAddMixedMultiStructure_of_boundedLocalNIP
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (rowRadius parameterRadius : ℚ≥0)
    (hlocal : NormFormula.IsBoundedLocalNIP (fun x y : E ↦ ‖x + y‖)) :
    MultiFormula.IsNIPInCompleteTheory
      (ballNormAddMixedMultiStructure (standardBanachBallStructure E)
        rowRadius parameterRadius)
      normAddMultiFormula := by
  apply MultiFormula.isNIPInCompleteTheory_of_no_finiteIPPatterns
  intro low high hgap hpatterns
  let denominator : ℝ :=
    rationalBallMetricBound (rowRadius + parameterRadius)
  have hdenominator : 0 < denominator :=
    rationalBallMetricBound_pos (rowRadius + parameterRadius)
  apply hlocal.not_hasIPPatternsInEveryDimension
    (R_x := (rowRadius : ℝ)) (R_y := (parameterRadius : ℝ))
    (low := low * denominator) (high := high * denominator)
    (mul_lt_mul_of_pos_right hgap hdenominator)
  intro n
  obtain ⟨rows, hip⟩ := hpatterns n
  refine ⟨fun i ↦ (rows i).1, fun i ↦ (rows i).2, ?_⟩
  intro subset
  obtain ⟨parameter, hhigh, hlow⟩ := hip subset
  refine ⟨⟨parameter.1, parameter.2⟩, ?_, ?_⟩
  · intro i hi
    have h := hhigh i hi
    change high ≤ normAddMultiFormula.binaryValue
      (ballNormAddMixedMultiStructure (standardBanachBallStructure E)
        rowRadius parameterRadius) (rows i) parameter at h
    rw [normAddMultiFormula_ballNormAddMixedMultiStructure_value,
      BallFormula.binaryValue, predicateFreeNormAddFormula_value] at h
    change high * denominator ≤ ‖(rows i).1 + parameter.1‖
    exact (le_div_iff₀ hdenominator).mp h
  · intro i hi
    have h := hlow i hi
    change normAddMultiFormula.binaryValue
      (ballNormAddMixedMultiStructure (standardBanachBallStructure E)
        rowRadius parameterRadius) (rows i) parameter ≤ low at h
    rw [normAddMultiFormula_ballNormAddMixedMultiStructure_value,
      BallFormula.binaryValue, predicateFreeNormAddFormula_value] at h
    change ‖(rows i).1 + parameter.1‖ ≤ low * denominator
    exact (div_le_iff₀ hdenominator).mp h

/-- NIP of the mixed-radius norm reduct implies NIP of the corresponding
typed norm-addition formula in the full complete ball theory. -/
theorem BallFormula.isNIPInCompleteTheory_of_mixedNormAddMulti
    (M : BallStructure.{u, 0} EmptyBallPredicate emptyBallPredicateRadius)
    (rowRadius parameterRadius : ℚ≥0)
    (hNIP : MultiFormula.IsNIPInCompleteTheory
      (ballNormAddMixedMultiStructure M rowRadius parameterRadius)
      normAddMultiFormula) :
    (predicateFreeNormAddFormula rowRadius parameterRadius).IsNIPInCompleteTheory M := by
  intro hIP
  exact hNIP
    (hasIPInMixedNormAddMultiTheory_of_hasIPInBallTheory M
      rowRadius parameterRadius hIP)

end

end NormFormula.ContinuousLogic
