import NormFormula.Analytic.XUniformConvex
import NormFormula.ContinuousLogic.XHilbertExpansion

/-!
# Parallelogram and midpoint sentences for the `X` expansion

The finite linear-combination fragment of `ExpansionSymbol` names the norms
of the row, parameter, sum, and difference.  This file uses those atoms to
write the auxiliary-Hilbert parallelogram identity and the paper's fixed
midpoint estimate as universal zero-valued sentences.  It proves the
sentences in the distinguished expansion and transfers their pointwise
consequences to every model of the same complete expanded theory.
-/

namespace NormFormula.X.ContinuousLanguage

noncomputable section

open scoped Topology
open NormFormula.ContinuousLogic

universe u v

/-- A bounded discrepancy for the normalized parallelogram identity.  The
four inputs are the Hilbert norms of `x+y`, `x-y`, `x`, and `y`, normalized
respectively by `2R`, `2R`, `R`, and `R`. -/
def parallelogramDiscrepancyTruth
    (values : Fin 4 → TruthValue) : TruthValue := by
  let expression : ℝ :=
    2 * ((values 0 : ℝ) ^ 2 + (values 1 : ℝ) ^ 2) -
      ((values 2 : ℝ) ^ 2 + (values 3 : ℝ) ^ 2)
  refine ⟨|expression| / 4, div_nonneg (abs_nonneg _) (by norm_num), ?_⟩
  apply (div_le_one (by norm_num : (0 : ℝ) < 4)).2
  have hsq (i : Fin 4) : (values i : ℝ) ^ 2 ≤ 1 := by
    nlinarith [(values i).2.1, (values i).2.2]
  have hs0 : 0 ≤ (values 0 : ℝ) ^ 2 := sq_nonneg _
  have hs1 : 0 ≤ (values 1 : ℝ) ^ 2 := sq_nonneg _
  have hs2 : 0 ≤ (values 2 : ℝ) ^ 2 := sq_nonneg _
  have hs3 : 0 ≤ (values 3 : ℝ) ^ 2 := sq_nonneg _
  rw [abs_le]
  constructor <;> dsimp [expression] <;>
    nlinarith [hsq 0, hsq 1, hsq 2, hsq 3]

@[simp]
theorem parallelogramDiscrepancyTruth_coe
    (values : Fin 4 → TruthValue) :
    (parallelogramDiscrepancyTruth values : ℝ) =
      |2 * ((values 0 : ℝ) ^ 2 + (values 1 : ℝ) ^ 2) -
        ((values 2 : ℝ) ^ 2 + (values 3 : ℝ) ^ 2)| / 4 :=
  rfl

/-- The normalized parallelogram discrepancy as a continuous connective. -/
def parallelogramDiscrepancyConnective : Connective 4 where
  toFun := parallelogramDiscrepancyTruth
  continuous_toFun := by
    have hreal : Continuous fun values : Fin 4 → TruthValue ↦
        |2 * ((values 0 : ℝ) ^ 2 + (values 1 : ℝ) ^ 2) -
          ((values 2 : ℝ) ^ 2 + (values 3 : ℝ) ^ 2)| / 4 := by
      fun_prop
    exact hreal.subtype_mk _

/-- Vanishing of the discrepancy is exactly the normalized parallelogram
identity. -/
theorem parallelogramDiscrepancyConnective_eq_zero_iff
    (values : Fin 4 → TruthValue) :
    parallelogramDiscrepancyConnective values = zeroTruthValue ↔
      2 * ((values 0 : ℝ) ^ 2 + (values 1 : ℝ) ^ 2) =
        (values 2 : ℝ) ^ 2 + (values 3 : ℝ) ^ 2 := by
  constructor
  · intro h
    have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) h
    change |2 * ((values 0 : ℝ) ^ 2 + (values 1 : ℝ) ^ 2) -
      ((values 2 : ℝ) ^ 2 + (values 3 : ℝ) ^ 2)| / 4 = 0 at hcoe
    have habs : |2 * ((values 0 : ℝ) ^ 2 + (values 1 : ℝ) ^ 2) -
        ((values 2 : ℝ) ^ 2 + (values 3 : ℝ) ^ 2)| = 0 := by
      exact (div_eq_zero_iff).1 hcoe |>.resolve_right (by norm_num)
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  · intro h
    apply Subtype.ext
    change |2 * ((values 0 : ℝ) ^ 2 + (values 1 : ℝ) ^ 2) -
      ((values 2 : ℝ) ^ 2 + (values 3 : ℝ) ^ 2)| / 4 = 0
    rw [h, sub_self, abs_zero, zero_div]

/-- A bounded violation of the normalized midpoint estimate.  The inputs are
`‖x+y‖/(2R)` and `‖x-y‖/(2R)`. -/
def midpointViolationTruth (values : Fin 2 → TruthValue) : TruthValue := by
  let expression : ℝ :=
    (values 0 : ℝ) ^ 2 + (1 / 3 : ℝ) * (values 1 : ℝ) ^ 2 - 1
  refine ⟨max 0 expression, le_max_left _ _, ?_⟩
  apply max_le
  · norm_num
  · have hsq0 : (values 0 : ℝ) ^ 2 ≤ 1 := by
      nlinarith [(values 0).2.1, (values 0).2.2]
    have hsq1 : (values 1 : ℝ) ^ 2 ≤ 1 := by
      nlinarith [(values 1).2.1, (values 1).2.2]
    dsimp [expression]
    nlinarith [sq_nonneg (values 1 : ℝ)]

@[simp]
theorem midpointViolationTruth_coe (values : Fin 2 → TruthValue) :
    (midpointViolationTruth values : ℝ) =
      max 0 ((values 0 : ℝ) ^ 2 +
        (1 / 3 : ℝ) * (values 1 : ℝ) ^ 2 - 1) :=
  rfl

/-- The midpoint violation as a continuous connective. -/
def midpointViolationConnective : Connective 2 where
  toFun := midpointViolationTruth
  continuous_toFun := by
    have hreal : Continuous fun values : Fin 2 → TruthValue ↦
        max 0 ((values 0 : ℝ) ^ 2 +
          (1 / 3 : ℝ) * (values 1 : ℝ) ^ 2 - 1) := by
      fun_prop
    exact hreal.subtype_mk _

/-- The midpoint violation vanishes exactly when the normalized fixed-modulus
inequality holds. -/
theorem midpointViolationConnective_eq_zero_iff
    (values : Fin 2 → TruthValue) :
    midpointViolationConnective values = zeroTruthValue ↔
      (values 0 : ℝ) ^ 2 + (1 / 3 : ℝ) * (values 1 : ℝ) ^ 2 ≤ 1 := by
  constructor
  · intro h
    have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) h
    change max 0 ((values 0 : ℝ) ^ 2 +
      (1 / 3 : ℝ) * (values 1 : ℝ) ^ 2 - 1) = 0 at hcoe
    have hle : (values 0 : ℝ) ^ 2 +
        (1 / 3 : ℝ) * (values 1 : ℝ) ^ 2 - 1 ≤
        max 0 ((values 0 : ℝ) ^ 2 +
          (1 / 3 : ℝ) * (values 1 : ℝ) ^ 2 - 1) :=
      le_max_right _ _
    linarith
  · intro h
    apply Subtype.ext
    change max 0 ((values 0 : ℝ) ^ 2 +
      (1 / 3 : ℝ) * (values 1 : ℝ) ^ 2 - 1) = 0
    rw [max_eq_left]
    linarith

/-- Auxiliary Hilbert norm of the row variable. -/
def hilbertRowFormula : MultiFormula ExpansionSymbol 1 1 :=
  .predicate .hilbertRow 0 0

/-- Auxiliary Hilbert norm of the parameter variable. -/
def hilbertParameterFormula : MultiFormula ExpansionSymbol 1 1 :=
  .predicate .hilbertParameter 0 0

/-- Auxiliary Hilbert norm of the difference. -/
def hilbertSubFormula : MultiFormula ExpansionSymbol 1 1 :=
  .predicate .hilbertSub 0 0

/-- Ambient norm of the difference. -/
def normSubFormula : MultiFormula ExpansionSymbol 1 1 :=
  .predicate .normSub 0 0

/-- The pointwise normalized auxiliary-Hilbert parallelogram discrepancy. -/
def parallelogramDiscrepancyFormula : MultiFormula ExpansionSymbol 1 1 :=
  .connective parallelogramDiscrepancyConnective
    ![hilbertFormula, hilbertSubFormula,
      hilbertRowFormula, hilbertParameterFormula]

/-- The universal auxiliary-Hilbert parallelogram sentence. -/
def parallelogramSentence : MultiSentence ExpansionSymbol :=
  universalBinarySentence parallelogramDiscrepancyFormula

/-- The pointwise normalized midpoint violation. -/
def midpointViolationFormula : MultiFormula ExpansionSymbol 1 1 :=
  .connective midpointViolationConnective ![normFormula, normSubFormula]

/-- The paper's fixed midpoint estimate as a universal sentence on the unit
ball. -/
def midpointSentence : MultiSentence ExpansionSymbol :=
  universalBinarySentence midpointViolationFormula

/-- The normalized auxiliary Hilbert norms satisfy the parallelogram identity
in the distinguished expansion. -/
theorem parallelogramDiscrepancyFormula_realize
    (R : ℝ) (hR : 0 < R)
    (rows : Fin 1 → PositiveNormBall XSpace R)
    (parameters : Fin 1 → PositiveNormBall XSpace R) :
    parallelogramDiscrepancyFormula.realize
        (expansionStructure R hR) rows parameters = zeroTruthValue := by
  apply (parallelogramDiscrepancyConnective_eq_zero_iff _).2
  have hpar := parallelogram_law_with_norm ℝ
    (toHilbert (rows 0).1) (toHilbert (parameters 0).1)
  have hadd : toHilbert ((rows 0).1 + (parameters 0).1) =
      toHilbert (rows 0).1 + toHilbert (parameters 0).1 :=
    linearEquivHilbertSum.map_add _ _
  have hsub : toHilbert ((rows 0).1 - (parameters 0).1) =
      toHilbert (rows 0).1 - toHilbert (parameters 0).1 :=
    linearEquivHilbertSum.map_sub _ _
  change 2 *
      ((‖toHilbert ((rows 0).1 + (parameters 0).1)‖ / (2 * R)) ^ 2 +
        (‖toHilbert ((rows 0).1 - (parameters 0).1)‖ / (2 * R)) ^ 2) =
    (‖toHilbert (rows 0).1‖ / R) ^ 2 +
      (‖toHilbert (parameters 0).1‖ / R) ^ 2
  rw [hadd, hsub]
  field_simp [ne_of_gt hR]
  nlinarith

/-- The universal parallelogram sentence has value zero in every positive
ball expansion of `XSpace`. -/
@[simp]
theorem parallelogramSentence_value (R : ℝ) (hR : 0 < R) :
    parallelogramSentence.value (expansionStructure R hR) = zeroTruthValue :=
  universalBinarySentence_value_eq_zero R hR _
    (parallelogramDiscrepancyFormula_realize R hR)

/-- The paper's analytic midpoint theorem makes every pointwise violation on
the concrete unit ball vanish. -/
theorem midpointViolationFormula_realize
    (rows : Fin 1 → PositiveNormBall XSpace 1)
    (parameters : Fin 1 → PositiveNormBall XSpace 1) :
    midpointViolationFormula.realize
        (expansionStructure 1 one_pos) rows parameters = zeroTruthValue := by
  apply (midpointViolationConnective_eq_zero_iff _).2
  have hmid := norm_midpoint_sq_le (x := (rows 0).1)
    (y := (parameters 0).1) (rows 0).2 (parameters 0).2
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hmid
  simp only [show (![normFormula, normSubFormula] (0 : Fin 2)) =
      normFormula from rfl,
    show (![normFormula, normSubFormula] (1 : Fin 2)) =
      normSubFormula from rfl]
  simp only [normFormula, normSubFormula, MultiFormula.realize,
    expansionStructure]
  simp only [normAddTruth_coe, normSubTruth]
  norm_num only [mul_one]
  nlinarith

/-- The universal midpoint sentence has value zero in the distinguished unit
ball expansion. -/
@[simp]
theorem midpointSentence_value :
    midpointSentence.value (expansionStructure 1 one_pos) = zeroTruthValue :=
  universalBinarySentence_value_eq_zero 1 one_pos _
    midpointViolationFormula_realize

/-- Same complete expanded theory transfers both the auxiliary-Hilbert
parallelogram identity and the midpoint estimate pointwise. -/
theorem parallelogram_and_midpoint_of_sameCompleteTheory
    (N : MultiStructure.{u, v} ExpansionSymbol)
    (hTheory : MultiSameCompleteTheory (expansionStructure 1 one_pos) N)
    (rows : Fin 1 → N.Row) (parameters : Fin 1 → N.Parameter) :
    2 * ((hilbertFormula.realize N rows parameters : ℝ) ^ 2 +
        (hilbertSubFormula.realize N rows parameters : ℝ) ^ 2) =
      (hilbertRowFormula.realize N rows parameters : ℝ) ^ 2 +
        (hilbertParameterFormula.realize N rows parameters : ℝ) ^ 2 ∧
    (normFormula.realize N rows parameters : ℝ) ^ 2 +
        (1 / 3 : ℝ) * (normSubFormula.realize N rows parameters : ℝ) ^ 2 ≤
      1 := by
  have hparSentence : parallelogramSentence.value N = zeroTruthValue := by
    calc
      parallelogramSentence.value N =
          parallelogramSentence.value (expansionStructure 1 one_pos) :=
        (hTheory parallelogramSentence).symm
      _ = zeroTruthValue := parallelogramSentence_value 1 one_pos
  have hmidSentence : midpointSentence.value N = zeroTruthValue := by
    calc
      midpointSentence.value N =
          midpointSentence.value (expansionStructure 1 one_pos) :=
        (hTheory midpointSentence).symm
      _ = zeroTruthValue := midpointSentence_value
  constructor
  · have hle := realize_le_universalBinarySentence N
      parallelogramDiscrepancyFormula rows parameters
    change parallelogramDiscrepancyFormula.realize N rows parameters ≤
      parallelogramSentence.value N at hle
    rw [hparSentence] at hle
    have hzero : parallelogramDiscrepancyFormula.realize N rows parameters =
        zeroTruthValue := le_antisymm hle
          (parallelogramDiscrepancyFormula.realize N rows parameters).2.1
    simpa using (parallelogramDiscrepancyConnective_eq_zero_iff _).1 hzero
  · have hle := realize_le_universalBinarySentence N
      midpointViolationFormula rows parameters
    change midpointViolationFormula.realize N rows parameters ≤
      midpointSentence.value N at hle
    rw [hmidSentence] at hle
    have hzero : midpointViolationFormula.realize N rows parameters =
        zeroTruthValue := le_antisymm hle
          (midpointViolationFormula.realize N rows parameters).2.1
    simpa using (midpointViolationConnective_eq_zero_iff _).1 hzero

end

end NormFormula.X.ContinuousLanguage
