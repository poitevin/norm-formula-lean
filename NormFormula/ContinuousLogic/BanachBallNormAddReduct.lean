import NormFormula.ContinuousLogic.BanachBallFormulaContinuity
import NormFormula.ContinuousLogic.FinitePatternTransfer
import NormFormula.ContinuousLogic.FullBanachBallTheoryIP
import NormFormula.ContinuousLogic.NormAdd

/-!
# Fixed-radius norm reducts of predicate-free Banach ball structures

At a fixed rational radius, the typed formula `d(x+y,0)` determines a
two-sorted one-predicate reduct.  This file translates the entire bounded
two-sorted syntax of that reduct into the predicate-free typed ball syntax.
Consequently, equality of complete ball theories implies equality of the
associated fixed-radius norm-reduct theories.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u v

/-- A constant typed context in which every variable ranges over the same
rational-radius ball. -/
def equalRadiusContext (radius : ℚ≥0) : (n : ℕ) → BallContext n
  | 0 => Fin.elim0
  | n + 1 => Fin.cons radius (equalRadiusContext radius n)

@[simp]
theorem equalRadiusContext_apply (radius : ℚ≥0) (n : ℕ) (i : Fin n) :
    equalRadiusContext radius n i = radius := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n induction =>
      exact Fin.cases rfl (fun j ↦ induction j) i

/-- Prepending the same radius to a constant context yields the next constant
context. -/
theorem cons_equalRadiusContext (radius : ℚ≥0) (n : ℕ) :
    Fin.cons radius (equalRadiusContext radius n) =
      equalRadiusContext radius (n + 1) :=
  rfl

/-- Transport only the output-radius index of a typed term. -/
def BallTerm.castRadius {n : ℕ} {context : BallContext n}
    {first second : ℚ≥0} (h : first = second)
    (term : BallTerm context first) : BallTerm context second :=
  h ▸ term

@[simp]
theorem BallTerm.realize_castRadius
    (S : RationalBallSystem.{u}) {n : ℕ} {context : BallContext n}
    {first second : ℚ≥0} (h : first = second)
    (term : BallTerm context first)
    (assignment : BallTerm.Assignment S context) :
    (term.castRadius h).realize S assignment =
      (h ▸ term.realize S assignment) := by
  subst second
  rfl

/-- A variable of a constant-radius context, with its output sort exposed as
the common radius. -/
def equalRadiusVariable (radius : ℚ≥0) {n : ℕ} (i : Fin n) :
    BallTerm (equalRadiusContext radius n) radius :=
  BallTerm.castRadius (equalRadiusContext_apply radius n i) (.variable i)

/-- Read one entry of a dependent constant-radius assignment at the exposed
common radius. -/
def equalRadiusAssignmentValue
    (S : RationalBallSystem.{u}) (radius : ℚ≥0) {n : ℕ}
    (assignment : BallTerm.Assignment S (equalRadiusContext radius n))
    (i : Fin n) : S.Ball radius :=
  equalRadiusContext_apply radius n i ▸ assignment i

@[simp]
theorem equalRadiusVariable_realize
    (S : RationalBallSystem.{u}) (radius : ℚ≥0) {n : ℕ} (i : Fin n)
    (assignment : BallTerm.Assignment S (equalRadiusContext radius n)) :
    (equalRadiusVariable radius i).realize S assignment =
      equalRadiusAssignmentValue S radius assignment i := by
  simp only [equalRadiusVariable, equalRadiusAssignmentValue,
    BallTerm.realize_castRadius, BallTerm.realize_variable]

/-- Prepend a new point to a dependent constant-radius assignment. -/
def equalRadiusAssignmentCons
    (S : RationalBallSystem.{u}) (radius : ℚ≥0) {n : ℕ}
    (x : S.Ball radius)
    (assignment : BallTerm.Assignment S (equalRadiusContext radius n)) :
    BallTerm.Assignment S (equalRadiusContext radius (n + 1)) := by
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact x
  · exact assignment j

theorem equalRadiusAssignmentCons_eq_finCons
    (S : RationalBallSystem.{u}) (radius : ℚ≥0) {n : ℕ}
    (x : S.Ball radius)
    (assignment : BallTerm.Assignment S (equalRadiusContext radius n)) :
    equalRadiusAssignmentCons S radius x assignment = Fin.cons x assignment := by
  funext i
  exact Fin.cases rfl (fun _ ↦ rfl) i

@[simp]
theorem equalRadiusAssignmentValue_cons_zero
    (S : RationalBallSystem.{u}) (radius : ℚ≥0) {n : ℕ}
    (x : S.Ball radius)
    (assignment : BallTerm.Assignment S (equalRadiusContext radius n)) :
    equalRadiusAssignmentValue S radius
      (equalRadiusAssignmentCons S radius x assignment) 0 = x := by
  rfl

@[simp]
theorem equalRadiusAssignmentValue_cons_succ
    (S : RationalBallSystem.{u}) (radius : ℚ≥0) {n : ℕ}
    (x : S.Ball radius)
    (assignment : BallTerm.Assignment S (equalRadiusContext radius n))
    (i : Fin n) :
    equalRadiusAssignmentValue S radius
        (equalRadiusAssignmentCons S radius x assignment) i.succ =
      equalRadiusAssignmentValue S radius assignment i := by
  rfl

/-- The one-predicate two-sorted norm reduct determined by the typed
distance-to-zero formula on two copies of one ball sort. -/
def ballNormAddMultiStructure
    (M : BallStructure.{u, 0} EmptyBallPredicate emptyBallPredicateRadius)
    (radius : ℚ≥0) : MultiStructure NormAddSymbol where
  Row := M.Ball radius
  Parameter := M.Ball radius
  rowNonempty := M.ballNonempty radius
  parameterNonempty := M.ballNonempty radius
  predicate
    | .norm => fun x y ↦
        (predicateFreeNormAddFormula radius radius).realize M
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))
  predicate_uniformContinuous := by
    intro symbol
    cases symbol
    have hassignment : UniformContinuous
        (fun p : M.Ball radius × M.Ball radius ↦
          (Fin.cons p.1 (Fin.cons p.2 (fun i : Fin 0 ↦ nomatch i)) :
            BallTerm.Assignment M.toRationalBallSystem
              (![(radius : ℚ≥0), radius] : BallContext 2))) := by
      apply uniformContinuous_pi.mpr
      intro i
      fin_cases i
      · exact uniformContinuous_fst
      · exact uniformContinuous_snd
    exact ((predicateFreeNormAddFormula radius radius).realize_uniformContinuous M).comp
      hassignment

@[simp]
theorem ballNormAddMultiStructure_predicate
    (M : BallStructure.{u, 0} EmptyBallPredicate emptyBallPredicateRadius)
    (radius : ℚ≥0) (x y : M.Ball radius) :
    (ballNormAddMultiStructure M radius).predicate .norm x y =
      (predicateFreeNormAddFormula radius radius).realize M
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) :=
  rfl

/-- Translate a two-sorted norm-reduct formula using explicit placements of
its row and parameter variables in one typed ball context. -/
def MultiFormula.toNormAddBallFormulaAux
    (radius : ℚ≥0) {rowVars parameterVars n : ℕ}
    (rowIndex : Fin rowVars → Fin n)
    (parameterIndex : Fin parameterVars → Fin n) :
    MultiFormula NormAddSymbol rowVars parameterVars →
      BallFormula EmptyBallPredicate emptyBallPredicateRadius
        (equalRadiusContext radius n)
  | .predicate .norm i j =>
      .distance
        (.add (equalRadiusVariable radius (rowIndex i))
          (equalRadiusVariable radius (parameterIndex j)))
        (.zero (radius + radius))
  | .constant value => .constant value
  | .connective gate formulas =>
      .connective gate fun i ↦
        (formulas i).toNormAddBallFormulaAux radius rowIndex parameterIndex
  | .iSupRow formula => by
      apply BallFormula.iSup radius
      exact formula.toNormAddBallFormulaAux radius
          (Fin.cons 0 fun i ↦ (rowIndex i).succ)
          (fun j ↦ (parameterIndex j).succ)
  | .iInfRow formula => by
      apply BallFormula.iInf radius
      exact formula.toNormAddBallFormulaAux radius
          (Fin.cons 0 fun i ↦ (rowIndex i).succ)
          (fun j ↦ (parameterIndex j).succ)
  | .iSupParameter formula => by
      apply BallFormula.iSup radius
      exact formula.toNormAddBallFormulaAux radius
          (fun i ↦ (rowIndex i).succ)
          (Fin.cons 0 fun j ↦ (parameterIndex j).succ)
  | .iInfParameter formula => by
      apply BallFormula.iInf radius
      exact formula.toNormAddBallFormulaAux radius
          (fun i ↦ (rowIndex i).succ)
          (Fin.cons 0 fun j ↦ (parameterIndex j).succ)

/-- Canonical translation with rows followed by parameters in the free
typed context. -/
def MultiFormula.toNormAddBallFormula
    (radius : ℚ≥0) {rowVars parameterVars : ℕ}
    (formula : MultiFormula NormAddSymbol rowVars parameterVars) :
    BallFormula EmptyBallPredicate emptyBallPredicateRadius
      (equalRadiusContext radius (rowVars + parameterVars)) :=
  formula.toNormAddBallFormulaAux radius
    (fun i ↦ Fin.castAdd parameterVars i)
    (fun j ↦ Fin.natAdd rowVars j)

/-- Realization of the explicit-index translation agrees with realization in
the fixed-radius norm reduct. -/
theorem MultiFormula.realize_toNormAddBallFormulaAux
    (M : BallStructure.{u, 0} EmptyBallPredicate emptyBallPredicateRadius)
    (radius : ℚ≥0) {rowVars parameterVars n : ℕ}
    (rowIndex : Fin rowVars → Fin n)
    (parameterIndex : Fin parameterVars → Fin n)
    (formula : MultiFormula NormAddSymbol rowVars parameterVars)
    (assignment : BallTerm.Assignment M.toRationalBallSystem
      (equalRadiusContext radius n)) :
    (formula.toNormAddBallFormulaAux radius rowIndex parameterIndex).realize
        M assignment =
      formula.realize (ballNormAddMultiStructure M radius)
        (fun i ↦ equalRadiusAssignmentValue M.toRationalBallSystem radius
          assignment (rowIndex i))
        (fun j ↦ equalRadiusAssignmentValue M.toRationalBallSystem radius
          assignment (parameterIndex j)) := by
  induction formula generalizing n with
  | predicate symbol i j =>
      cases symbol
      simp only [toNormAddBallFormulaAux, equalRadiusVariable_realize,
        MultiFormula.realize,
        ballNormAddMultiStructure_predicate, predicateFreeNormAddFormula,
        BallFormula.realize_distance, BallTerm.binaryAddTerm,
        BallTerm.realize, Fin.cons_zero]
      have hsnd :
          (Fin.cons
              (equalRadiusAssignmentValue M.toRationalBallSystem radius
                assignment (rowIndex i))
              (Fin.cons
                (equalRadiusAssignmentValue M.toRationalBallSystem radius
                  assignment (parameterIndex j))
                (fun k : Fin 0 ↦ nomatch k)) :
            BallTerm.Assignment M.toRationalBallSystem
              (![(radius : ℚ≥0), radius] : BallContext 2)) (1 : Fin 2) =
            equalRadiusAssignmentValue M.toRationalBallSystem radius
              assignment (parameterIndex j) := by
        rfl
      rw [hsnd]
  | constant value =>
      rfl
  | connective gate formulas induction =>
      simp only [toNormAddBallFormulaAux, BallFormula.realize,
        MultiFormula.realize]
      congr 1
      funext i
      exact induction i rowIndex parameterIndex assignment
  | iSupRow formula induction =>
      simp only [toNormAddBallFormulaAux, BallFormula.realize,
        MultiFormula.realize]
      apply iSup_congr
      intro x
      let extendedRowIndex : Fin (_ + 1) → Fin (n + 1) :=
        Fin.cons (0 : Fin (n + 1)) (fun i ↦ (rowIndex i).succ)
      have hih := induction
          extendedRowIndex
          (fun j ↦ (parameterIndex j).succ)
          (equalRadiusAssignmentCons M.toRationalBallSystem radius x assignment)
      have hrows :
          (fun i ↦ equalRadiusAssignmentValue M.toRationalBallSystem radius
            (equalRadiusAssignmentCons M.toRationalBallSystem radius x assignment)
            (extendedRowIndex i)) =
          Fin.cons x (fun i ↦ equalRadiusAssignmentValue
            M.toRationalBallSystem radius assignment (rowIndex i)) := by
        funext i
        exact Fin.cases
          (equalRadiusAssignmentValue_cons_zero _ _ _ _)
          (fun k ↦ equalRadiusAssignmentValue_cons_succ _ _ _ _ _) i
      have hparameters :
          (fun j ↦ equalRadiusAssignmentValue M.toRationalBallSystem radius
            (equalRadiusAssignmentCons M.toRationalBallSystem radius x assignment)
            (parameterIndex j).succ) =
          (fun j ↦ equalRadiusAssignmentValue M.toRationalBallSystem radius
            assignment (parameterIndex j)) := by
        funext j
        exact equalRadiusAssignmentValue_cons_succ _ _ _ _ _
      rw [hrows, hparameters] at hih
      have hrealize := congrArg
        (fun a ↦ (formula.toNormAddBallFormulaAux radius
          extendedRowIndex
          (fun j ↦ (parameterIndex j).succ)).realize M a)
        (equalRadiusAssignmentCons_eq_finCons
          M.toRationalBallSystem radius x assignment)
      exact hrealize.symm.trans hih

  | iInfRow formula induction =>
      simp only [toNormAddBallFormulaAux, BallFormula.realize,
        MultiFormula.realize]
      apply iInf_congr
      intro x
      let extendedRowIndex : Fin (_ + 1) → Fin (n + 1) :=
        Fin.cons (0 : Fin (n + 1)) (fun i ↦ (rowIndex i).succ)
      have hih := induction
          extendedRowIndex
          (fun j ↦ (parameterIndex j).succ)
          (equalRadiusAssignmentCons M.toRationalBallSystem radius x assignment)
      have hrows :
          (fun i ↦ equalRadiusAssignmentValue M.toRationalBallSystem radius
            (equalRadiusAssignmentCons M.toRationalBallSystem radius x assignment)
            (extendedRowIndex i)) =
          Fin.cons x (fun i ↦ equalRadiusAssignmentValue
            M.toRationalBallSystem radius assignment (rowIndex i)) := by
        funext i
        exact Fin.cases
          (equalRadiusAssignmentValue_cons_zero _ _ _ _)
          (fun k ↦ equalRadiusAssignmentValue_cons_succ _ _ _ _ _) i
      have hparameters :
          (fun j ↦ equalRadiusAssignmentValue M.toRationalBallSystem radius
            (equalRadiusAssignmentCons M.toRationalBallSystem radius x assignment)
            (parameterIndex j).succ) =
          (fun j ↦ equalRadiusAssignmentValue M.toRationalBallSystem radius
            assignment (parameterIndex j)) := by
        funext j
        exact equalRadiusAssignmentValue_cons_succ _ _ _ _ _
      rw [hrows, hparameters] at hih
      have hrealize := congrArg
        (fun a ↦ (formula.toNormAddBallFormulaAux radius
          extendedRowIndex
          (fun j ↦ (parameterIndex j).succ)).realize M a)
        (equalRadiusAssignmentCons_eq_finCons
          M.toRationalBallSystem radius x assignment)
      exact hrealize.symm.trans hih

  | iSupParameter formula induction =>
      simp only [toNormAddBallFormulaAux, BallFormula.realize,
        MultiFormula.realize]
      apply iSup_congr
      intro y
      let extendedParameterIndex : Fin (_ + 1) → Fin (n + 1) :=
        Fin.cons (0 : Fin (n + 1)) (fun j ↦ (parameterIndex j).succ)
      have hih := induction
          (fun i ↦ (rowIndex i).succ)
          extendedParameterIndex
          (equalRadiusAssignmentCons M.toRationalBallSystem radius y assignment)
      have hrows :
          (fun i ↦ equalRadiusAssignmentValue M.toRationalBallSystem radius
            (equalRadiusAssignmentCons M.toRationalBallSystem radius y assignment)
            (rowIndex i).succ) =
          (fun i ↦ equalRadiusAssignmentValue M.toRationalBallSystem radius
            assignment (rowIndex i)) := by
        funext i
        exact equalRadiusAssignmentValue_cons_succ _ _ _ _ _
      have hparameters :
          (fun j ↦ equalRadiusAssignmentValue M.toRationalBallSystem radius
            (equalRadiusAssignmentCons M.toRationalBallSystem radius y assignment)
            (extendedParameterIndex j)) =
          Fin.cons y (fun j ↦ equalRadiusAssignmentValue
            M.toRationalBallSystem radius assignment (parameterIndex j)) := by
        funext j
        exact Fin.cases
          (equalRadiusAssignmentValue_cons_zero _ _ _ _)
          (fun k ↦ equalRadiusAssignmentValue_cons_succ _ _ _ _ _) j
      rw [hrows, hparameters] at hih
      have hrealize := congrArg
        (fun a ↦ (formula.toNormAddBallFormulaAux radius
          (fun i ↦ (rowIndex i).succ)
          extendedParameterIndex).realize M a)
        (equalRadiusAssignmentCons_eq_finCons
          M.toRationalBallSystem radius y assignment)
      exact hrealize.symm.trans hih

  | iInfParameter formula induction =>
      simp only [toNormAddBallFormulaAux, BallFormula.realize,
        MultiFormula.realize]
      apply iInf_congr
      intro y
      let extendedParameterIndex : Fin (_ + 1) → Fin (n + 1) :=
        Fin.cons (0 : Fin (n + 1)) (fun j ↦ (parameterIndex j).succ)
      have hih := induction
          (fun i ↦ (rowIndex i).succ)
          extendedParameterIndex
          (equalRadiusAssignmentCons M.toRationalBallSystem radius y assignment)
      have hrows :
          (fun i ↦ equalRadiusAssignmentValue M.toRationalBallSystem radius
            (equalRadiusAssignmentCons M.toRationalBallSystem radius y assignment)
            (rowIndex i).succ) =
          (fun i ↦ equalRadiusAssignmentValue M.toRationalBallSystem radius
            assignment (rowIndex i)) := by
        funext i
        exact equalRadiusAssignmentValue_cons_succ _ _ _ _ _
      have hparameters :
          (fun j ↦ equalRadiusAssignmentValue M.toRationalBallSystem radius
            (equalRadiusAssignmentCons M.toRationalBallSystem radius y assignment)
            (extendedParameterIndex j)) =
          Fin.cons y (fun j ↦ equalRadiusAssignmentValue
            M.toRationalBallSystem radius assignment (parameterIndex j)) := by
        funext j
        exact Fin.cases
          (equalRadiusAssignmentValue_cons_zero _ _ _ _)
          (fun k ↦ equalRadiusAssignmentValue_cons_succ _ _ _ _ _) j
      rw [hrows, hparameters] at hih
      have hrealize := congrArg
        (fun a ↦ (formula.toNormAddBallFormulaAux radius
          (fun i ↦ (rowIndex i).succ)
          extendedParameterIndex).realize M a)
        (equalRadiusAssignmentCons_eq_finCons
          M.toRationalBallSystem radius y assignment)
      exact hrealize.symm.trans hih

/-- The sentence-level translation uses the unique maps from its empty free
contexts. -/
def MultiSentence.toNormAddBallSentence
    (radius : ℚ≥0) (sentence : MultiSentence NormAddSymbol) :
    BallSentence EmptyBallPredicate emptyBallPredicateRadius :=
  sentence.toNormAddBallFormulaAux radius
    (fun i : Fin 0 ↦ nomatch i) (fun j : Fin 0 ↦ nomatch j)

/-- Sentence values are preserved by the fixed-radius syntax translation. -/
theorem MultiSentence.value_toNormAddBallFormula
    (M : BallStructure.{u, 0} EmptyBallPredicate emptyBallPredicateRadius)
    (radius : ℚ≥0) (sentence : MultiSentence NormAddSymbol) :
    BallSentence.value (sentence.toNormAddBallSentence radius) M =
      sentence.value (ballNormAddMultiStructure M radius) := by
  unfold MultiSentence.toNormAddBallSentence BallSentence.value MultiSentence.value
  have h := sentence.realize_toNormAddBallFormulaAux M radius
    (fun i : Fin 0 ↦ nomatch i) (fun j : Fin 0 ↦ nomatch j)
    (fun k : Fin 0 ↦ nomatch k)
  have hRows :
      (fun i : Fin 0 ↦ equalRadiusAssignmentValue M.toRationalBallSystem radius
        (fun k : Fin 0 ↦ nomatch k) (nomatch i)) =
        (Fin.elim0 : Fin 0 → (ballNormAddMultiStructure M radius).Row) :=
    Subsingleton.elim _ _
  rw [hRows] at h
  exact h

/-- Same complete typed ball theory implies the same complete theory for
every associated fixed-radius norm reduct. -/
theorem ballSameCompleteTheory_normAddMultiStructure
    (M : BallStructure.{u, 0} EmptyBallPredicate emptyBallPredicateRadius)
    (N : BallStructure.{v, 0} EmptyBallPredicate emptyBallPredicateRadius)
    (radius : ℚ≥0) (hTheory : BallSameCompleteTheory M N) :
    MultiSameCompleteTheory (ballNormAddMultiStructure M radius)
      (ballNormAddMultiStructure N radius) := by
  intro sentence
  rw [← MultiSentence.value_toNormAddBallFormula,
    ← MultiSentence.value_toNormAddBallFormula]
  exact hTheory (sentence.toNormAddBallSentence radius)

/-- The distinguished atom of the fixed-radius reduct has exactly the typed
norm-addition value. -/
@[simp]
theorem normAddMultiFormula_ballNormAddMultiStructure_value
    (M : BallStructure.{u, 0} EmptyBallPredicate emptyBallPredicateRadius)
    (radius : ℚ≥0) (x y : M.Ball radius) :
    normAddMultiFormula.binaryValue (ballNormAddMultiStructure M radius) x y =
      (predicateFreeNormAddFormula radius radius).binaryValue M x y :=
  rfl

/-- A typed infinite norm-addition witness is the same witness in the
associated fixed-radius two-sorted reduct. -/
theorem hasInfiniteIPWitness_normAddMultiStructure_iff
    (M : BallStructure.{u, 0} EmptyBallPredicate emptyBallPredicateRadius)
    (radius : ℚ≥0) (low high : ℝ) :
    (predicateFreeNormAddFormula radius radius).HasInfiniteIPWitness
        M low high ↔
      MultiFormula.HasInfiniteIPWitness
        (ballNormAddMultiStructure M radius) normAddMultiFormula low high :=
  Iff.rfl

/-- Complete-theory IP in the full ball language descends to complete-theory
IP of the associated fixed-radius norm reduct. -/
theorem hasIPInNormAddMultiTheory_of_hasIPInBallTheory
    (M : BallStructure.{u, 0} EmptyBallPredicate emptyBallPredicateRadius)
    (radius : ℚ≥0)
    (hIP : (predicateFreeNormAddFormula radius radius).HasIPInCompleteTheory M) :
    MultiFormula.HasIPInCompleteTheory
      (ballNormAddMultiStructure M radius) normAddMultiFormula := by
  obtain ⟨N, hTheory, low, high, hgap, hWitness⟩ := hIP
  refine ⟨ballNormAddMultiStructure N radius,
    ballSameCompleteTheory_normAddMultiStructure M N radius hTheory,
    low, high, hgap, ?_⟩
  exact (hasInfiniteIPWitness_normAddMultiStructure_iff
    N radius low high).mp hWitness

/-- Concrete bounded-local NIP of the ambient norm-addition function proves
complete-theory NIP for the fixed-radius reduct of its standard Banach ball
structure.  The proof passes through home-model finite patterns, so it does
not assume that an arbitrary same-theory ball structure is itself a Banach
space. -/
theorem normAddMultiFormula_isNIPInCompleteTheory_ballNormAddMultiStructure_of_boundedLocalNIP
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (radius : ℚ≥0)
    (hlocal : NormFormula.IsBoundedLocalNIP (fun x y : E ↦ ‖x + y‖)) :
    MultiFormula.IsNIPInCompleteTheory
      (ballNormAddMultiStructure (standardBanachBallStructure E) radius)
      normAddMultiFormula := by
  apply MultiFormula.isNIPInCompleteTheory_of_no_finiteIPPatterns
  intro low high hgap hpatterns
  let denominator : ℝ := rationalBallMetricBound (radius + radius)
  have hdenominator : 0 < denominator :=
    rationalBallMetricBound_pos (radius + radius)
  apply hlocal.not_hasIPPatternsInEveryDimension
    (R_x := (radius : ℝ)) (R_y := (radius : ℝ))
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
      (ballNormAddMultiStructure (standardBanachBallStructure E) radius)
      (rows i) parameter at h
    rw [normAddMultiFormula_ballNormAddMultiStructure_value,
      BallFormula.binaryValue, predicateFreeNormAddFormula_value] at h
    change high * denominator ≤ ‖(rows i).1 + parameter.1‖
    exact (le_div_iff₀ hdenominator).mp h
  · intro i hi
    have h := hlow i hi
    change normAddMultiFormula.binaryValue
      (ballNormAddMultiStructure (standardBanachBallStructure E) radius)
      (rows i) parameter ≤ low at h
    rw [normAddMultiFormula_ballNormAddMultiStructure_value,
      BallFormula.binaryValue, predicateFreeNormAddFormula_value] at h
    change ‖(rows i).1 + parameter.1‖ ≤ low * denominator
    exact (div_le_iff₀ hdenominator).mp h

/-- NIP of the fixed-radius norm reduct implies NIP of the corresponding
typed norm-addition formula in the full complete ball theory. -/
theorem BallFormula.isNIPInCompleteTheory_of_normAddMulti
    (M : BallStructure.{u, 0} EmptyBallPredicate emptyBallPredicateRadius)
    (radius : ℚ≥0)
    (hNIP : MultiFormula.IsNIPInCompleteTheory
      (ballNormAddMultiStructure M radius) normAddMultiFormula) :
    (predicateFreeNormAddFormula radius radius).IsNIPInCompleteTheory M := by
  intro hIP
  exact hNIP (hasIPInNormAddMultiTheory_of_hasIPInBallTheory M radius hIP)

end

end NormFormula.ContinuousLogic
