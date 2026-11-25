import NormFormula.Analytic.XUniformConvex
import NormFormula.ContinuousLogic.XHilbertBallExpansion

/-!
# Parallelogram and midpoint sentences in the ball-sorted `X` expansion

This file lifts the remaining geometric axioms of the paper's expanded
theory to the genuine rational-ball language.  Since a term in the
radius-`r + r` sort is normalized by that sort's metric bound, while its two
inputs are normalized by the radius-`r` bound, the parallelogram connective
records both scale factors explicitly.  The midpoint connective similarly
undoes the normalization of the radius-two sum and difference terms.

Both universal sentences have value zero in the distinguished expansion of
`XSpace`, and equality of complete ball-sorted theories transfers their
pointwise consequences to every same-theory structure.
-/

namespace NormFormula.X.BallLanguage

noncomputable section

open scoped Topology
open NormFormula.ContinuousLogic

universe u

/-- A bounded discrepancy for the auxiliary-Hilbert parallelogram identity.
The first two inputs are normalized on the radius-`r+r` output sort and the
last two on the radius-`r` input sort. -/
def parallelogramDiscrepancyTruth (r : ℚ≥0)
    (values : Fin 4 → TruthValue) : TruthValue := by
  let inputScale := rationalBallMetricBound r
  let outputScale := rationalBallMetricBound (r + r)
  let expression : ℝ :=
    outputScale ^ 2 *
        ((values 0 : ℝ) ^ 2 + (values 1 : ℝ) ^ 2) -
      2 * inputScale ^ 2 *
        ((values 2 : ℝ) ^ 2 + (values 3 : ℝ) ^ 2)
  let bound : ℝ := 2 * outputScale ^ 2 + 4 * inputScale ^ 2
  have hbound : 0 < bound := by
    dsimp [bound, inputScale, outputScale]
    nlinarith [sq_pos_of_pos (rationalBallMetricBound_pos r),
      sq_pos_of_pos (rationalBallMetricBound_pos (r + r))]
  refine ⟨|expression| / bound,
    div_nonneg (abs_nonneg _) hbound.le, ?_⟩
  apply (div_le_one hbound).2
  have hsq (i : Fin 4) : (values i : ℝ) ^ 2 ≤ 1 := by
    nlinarith [(values i).2.1, (values i).2.2]
  have hsq_nonneg (i : Fin 4) : 0 ≤ (values i : ℝ) ^ 2 :=
    sq_nonneg _
  rw [abs_le]
  constructor <;>
    dsimp [expression, bound, inputScale, outputScale] <;>
    nlinarith [hsq 0, hsq 1, hsq 2, hsq 3,
      hsq_nonneg 0, hsq_nonneg 1, hsq_nonneg 2, hsq_nonneg 3,
      (rationalBallMetricBound_pos r).le,
      (rationalBallMetricBound_pos (r + r)).le,
      sq_nonneg (rationalBallMetricBound r),
      sq_nonneg (rationalBallMetricBound (r + r))]


/-- The radius-aware parallelogram discrepancy as a continuous connective. -/
def parallelogramDiscrepancyConnective (r : ℚ≥0) : Connective 4 where
  toFun := parallelogramDiscrepancyTruth r
  continuous_toFun := by
    have hreal : Continuous fun values : Fin 4 → TruthValue ↦
        |rationalBallMetricBound (r + r) ^ 2 *
            ((values 0 : ℝ) ^ 2 + (values 1 : ℝ) ^ 2) -
          2 * rationalBallMetricBound r ^ 2 *
            ((values 2 : ℝ) ^ 2 + (values 3 : ℝ) ^ 2)| /
          (2 * rationalBallMetricBound (r + r) ^ 2 +
            4 * rationalBallMetricBound r ^ 2) := by
      fun_prop
    exact hreal.subtype_mk _

/-- Vanishing of the radius-aware discrepancy is exactly the normalized
parallelogram identity. -/
theorem parallelogramDiscrepancyConnective_eq_zero_iff
    (r : ℚ≥0) (values : Fin 4 → TruthValue) :
    parallelogramDiscrepancyConnective r values = zeroTruthValue ↔
      rationalBallMetricBound (r + r) ^ 2 *
          ((values 0 : ℝ) ^ 2 + (values 1 : ℝ) ^ 2) =
        2 * rationalBallMetricBound r ^ 2 *
          ((values 2 : ℝ) ^ 2 + (values 3 : ℝ) ^ 2) := by
  have hdenom : 2 * rationalBallMetricBound (r + r) ^ 2 +
      4 * rationalBallMetricBound r ^ 2 ≠ 0 := by
    have hpos : 0 < 2 * rationalBallMetricBound (r + r) ^ 2 +
        4 * rationalBallMetricBound r ^ 2 := by
      nlinarith [sq_pos_of_pos (rationalBallMetricBound_pos r),
        sq_pos_of_pos (rationalBallMetricBound_pos (r + r))]
    exact ne_of_gt hpos
  constructor
  · intro h
    have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) h
    change |_ - _| / _ = 0 at hcoe
    have habs : |rationalBallMetricBound (r + r) ^ 2 *
          ((values 0 : ℝ) ^ 2 + (values 1 : ℝ) ^ 2) -
        2 * rationalBallMetricBound r ^ 2 *
          ((values 2 : ℝ) ^ 2 + (values 3 : ℝ) ^ 2)| = 0 :=
      (div_eq_zero_iff).1 hcoe |>.resolve_right hdenom
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  · intro h
    apply Subtype.ext
    change |_ - _| / _ = 0
    rw [h, sub_self, abs_zero, zero_div]

/-- Auxiliary Hilbert norm of the sum of two radius-`r` variables. -/
def hilbertAddFormula (r : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius (![r, r] : BallContext 2) :=
  hilbertNormFormula (BallTerm.binaryAddTerm r r)

/-- Auxiliary Hilbert norm of the difference of two radius-`r` variables. -/
def hilbertSubFormula (r : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius (![r, r] : BallContext 2) :=
  hilbertNormFormula (BallTerm.binarySubTerm r)

/-- Auxiliary Hilbert norm of the first radius-`r` variable. -/
def hilbertFirstFormula (r : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius (![r, r] : BallContext 2) :=
  hilbertNormFormula (BallTerm.variable 0)

/-- Auxiliary Hilbert norm of the second radius-`r` variable. -/
def hilbertSecondFormula (r : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius (![r, r] : BallContext 2) :=
  hilbertNormFormula (BallTerm.variable 1)

/-- The pointwise typed auxiliary-Hilbert parallelogram discrepancy. -/
def parallelogramDiscrepancyFormula (r : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius (![r, r] : BallContext 2) :=
  .connective (parallelogramDiscrepancyConnective r)
    ![hilbertAddFormula r, hilbertSubFormula r,
      hilbertFirstFormula r, hilbertSecondFormula r]

/-- Universal closure of a formula with two variables in the same ball
sort. -/
def universalBinarySentence (r : ℚ≥0)
    (formula : BallFormula PredicateSymbol predicateRadius
      (![r, r] : BallContext 2)) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup r (.iSup r formula)

/-- The universal typed auxiliary-Hilbert parallelogram sentence on the
radius-`r` sort. -/
def parallelogramSentence (r : ℚ≥0) :
    BallSentence PredicateSymbol predicateRadius :=
  universalBinarySentence r (parallelogramDiscrepancyFormula r)

/-- A bounded violation of the unit-ball midpoint estimate.  Both inputs are
ambient norms of radius-two terms, hence are normalized by the metric bound
`4`; undoing that normalization gives the coefficients `4` and `4/3`. -/
def midpointViolationTruth (values : Fin 2 → TruthValue) : TruthValue := by
  let expression : ℝ :=
    4 * (values 0 : ℝ) ^ 2 +
      (4 / 3 : ℝ) * (values 1 : ℝ) ^ 2 - 1
  refine ⟨max 0 expression / (16 / 3 : ℝ),
    div_nonneg (le_max_left _ _) (by norm_num), ?_⟩
  apply (div_le_one (by norm_num : (0 : ℝ) < 16 / 3)).2
  apply max_le
  · norm_num
  · have hsq0 : (values 0 : ℝ) ^ 2 ≤ 1 := by
      nlinarith [(values 0).2.1, (values 0).2.2]
    have hsq1 : (values 1 : ℝ) ^ 2 ≤ 1 := by
      nlinarith [(values 1).2.1, (values 1).2.2]
    dsimp [expression]
    nlinarith [sq_nonneg (values 0 : ℝ), sq_nonneg (values 1 : ℝ)]


/-- The typed unit-ball midpoint violation as a continuous connective. -/
def midpointViolationConnective : Connective 2 where
  toFun := midpointViolationTruth
  continuous_toFun := by
    have hreal : Continuous fun values : Fin 2 → TruthValue ↦
        max 0 (4 * (values 0 : ℝ) ^ 2 +
          (4 / 3 : ℝ) * (values 1 : ℝ) ^ 2 - 1) / (16 / 3 : ℝ) := by
      fun_prop
    exact hreal.subtype_mk _

/-- Vanishing of the midpoint violation is exactly the normalized fixed
midpoint inequality. -/
theorem midpointViolationConnective_eq_zero_iff
    (values : Fin 2 → TruthValue) :
    midpointViolationConnective values = zeroTruthValue ↔
      4 * (values 0 : ℝ) ^ 2 +
        (4 / 3 : ℝ) * (values 1 : ℝ) ^ 2 ≤ 1 := by
  constructor
  · intro h
    have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) h
    change max 0 (_ - 1) / (16 / 3 : ℝ) = 0 at hcoe
    have hmax : max 0 (4 * (values 0 : ℝ) ^ 2 +
        (4 / 3 : ℝ) * (values 1 : ℝ) ^ 2 - 1) = 0 :=
      (div_eq_zero_iff).1 hcoe |>.resolve_right (by norm_num)
    have hle := le_max_right 0
      (4 * (values 0 : ℝ) ^ 2 +
        (4 / 3 : ℝ) * (values 1 : ℝ) ^ 2 - 1)
    linarith
  · intro h
    apply Subtype.ext
    change max 0 (_ - 1) / (16 / 3 : ℝ) = 0
    rw [max_eq_left]
    · norm_num
    · linarith

/-- The pointwise typed midpoint violation on two unit-ball variables. -/
def ambientAddUnitFormula :
    BallFormula PredicateSymbol predicateRadius
      (![(1 : ℚ≥0), (1 : ℚ≥0)] : BallContext 2) :=
  ambientNormFormula (BallTerm.binaryAddTerm 1 1)

/-- Ambient norm of the difference of two unit-ball variables. -/
def ambientSubUnitFormula :
    BallFormula PredicateSymbol predicateRadius
      (![(1 : ℚ≥0), (1 : ℚ≥0)] : BallContext 2) :=
  ambientNormFormula (BallTerm.binarySubTerm 1)

/-- Concrete value of the normalized ambient norm of the unit-ball sum. -/
theorem ambientAddUnitFormula_value
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![(1 : ℚ≥0), (1 : ℚ≥0)] : BallContext 2)) :
    (ambientAddUnitFormula.realize expansionStructure assignment : ℝ) =
      ‖(assignment 0).1 + (assignment 1).1‖ /
        rationalBallMetricBound (1 + 1) := by
  unfold ambientAddUnitFormula
  rw [ambientNormFormula_value]
  exact congrArg (fun z : XSpace ↦ ‖z‖ /
    rationalBallMetricBound (1 + 1))
      (BallTerm.binaryAddTerm_standardValue 1 1 assignment)

/-- Concrete value of the normalized ambient norm of the unit-ball
difference. -/
theorem ambientSubUnitFormula_value
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![(1 : ℚ≥0), (1 : ℚ≥0)] : BallContext 2)) :
    (ambientSubUnitFormula.realize expansionStructure assignment : ℝ) =
      ‖(assignment 0).1 - (assignment 1).1‖ /
        rationalBallMetricBound (1 + 1) := by
  unfold ambientSubUnitFormula
  rw [ambientNormFormula_value]
  exact congrArg (fun z : XSpace ↦ ‖z‖ /
    rationalBallMetricBound (1 + 1))
      (BallTerm.binarySubTerm_standardValue 1 assignment)

/-- The pointwise typed midpoint violation on two unit-ball variables. -/
def midpointViolationFormula :
    BallFormula PredicateSymbol predicateRadius
      (![(1 : ℚ≥0), (1 : ℚ≥0)] : BallContext 2) :=
  .connective midpointViolationConnective
    ![ambientAddUnitFormula, ambientSubUnitFormula]

/-- The paper's fixed midpoint estimate as a universal typed sentence on the
unit ball. -/
def midpointSentence : BallSentence PredicateSymbol predicateRadius :=
  universalBinarySentence 1 midpointViolationFormula

/-- Every pointwise binary instance is bounded by its universal closure. -/
theorem realize_le_universalBinarySentence
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (r : ℚ≥0)
    (formula : BallFormula PredicateSymbol predicateRadius
      (![r, r] : BallContext 2))
    (x y : M.Ball r) :
    formula.realize M
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) ≤
      (universalBinarySentence r formula).value M := by
  apply le_trans
  · exact le_iSup
      (fun z : M.Ball r ↦ formula.realize M
        (Fin.cons z (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) x
  · exact le_iSup
      (fun z : M.Ball r ↦ ⨆ w : M.Ball r,
        formula.realize M
          (Fin.cons w (Fin.cons z (fun i : Fin 0 ↦ nomatch i)))) y

/-- The auxiliary Hilbert norm satisfies the typed parallelogram identity
pointwise in the distinguished expansion. -/
theorem parallelogramDiscrepancyFormula_realize
    (r : ℚ≥0)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r, r] : BallContext 2)) :
    (parallelogramDiscrepancyFormula r).realize
        expansionStructure assignment = zeroTruthValue := by
  apply (parallelogramDiscrepancyConnective_eq_zero_iff r _).2
  simp only [show (![hilbertAddFormula r, hilbertSubFormula r,
      hilbertFirstFormula r, hilbertSecondFormula r] (0 : Fin 4)) =
        hilbertAddFormula r from rfl,
    show (![hilbertAddFormula r, hilbertSubFormula r,
      hilbertFirstFormula r, hilbertSecondFormula r] (1 : Fin 4)) =
        hilbertSubFormula r from rfl,
    show (![hilbertAddFormula r, hilbertSubFormula r,
      hilbertFirstFormula r, hilbertSecondFormula r] (2 : Fin 4)) =
        hilbertFirstFormula r from rfl,
    show (![hilbertAddFormula r, hilbertSubFormula r,
      hilbertFirstFormula r, hilbertSecondFormula r] (3 : Fin 4)) =
        hilbertSecondFormula r from rfl]
  change rationalBallMetricBound (r + r) ^ 2 *
      ((‖toHilbert ((assignment 0).1 + (assignment 1).1)‖ /
          rationalBallMetricBound (r + r)) ^ 2 +
        (‖toHilbert ((assignment 0).1 - (assignment 1).1)‖ /
          rationalBallMetricBound (r + r)) ^ 2) =
    2 * rationalBallMetricBound r ^ 2 *
      ((‖toHilbert (assignment 0).1‖ / rationalBallMetricBound r) ^ 2 +
        (‖toHilbert (assignment 1).1‖ / rationalBallMetricBound r) ^ 2)
  have hpar := parallelogram_law_with_norm ℝ
    (toHilbert (assignment 0).1) (toHilbert (assignment 1).1)
  have hadd : toHilbert ((assignment 0).1 + (assignment 1).1) =
      toHilbert (assignment 0).1 + toHilbert (assignment 1).1 :=
    linearEquivHilbertSum.map_add _ _
  have hsub : toHilbert ((assignment 0).1 - (assignment 1).1) =
      toHilbert (assignment 0).1 - toHilbert (assignment 1).1 :=
    linearEquivHilbertSum.map_sub _ _
  rw [hadd, hsub]
  have hscaled (scale first second : ℝ) (hscale : scale ≠ 0) :
      scale ^ 2 * ((first / scale) ^ 2 + (second / scale) ^ 2) =
        first ^ 2 + second ^ 2 := by
    field_simp [hscale]
  have hscaledTwo (scale first second : ℝ) (hscale : scale ≠ 0) :
      2 * scale ^ 2 * ((first / scale) ^ 2 + (second / scale) ^ 2) =
        2 * (first ^ 2 + second ^ 2) := by
    rw [mul_assoc, hscaled scale first second hscale]
  calc
    rationalBallMetricBound (r + r) ^ 2 *
          ((‖toHilbert (assignment 0).1 + toHilbert (assignment 1).1‖ /
              rationalBallMetricBound (r + r)) ^ 2 +
            (‖toHilbert (assignment 0).1 - toHilbert (assignment 1).1‖ /
              rationalBallMetricBound (r + r)) ^ 2) =
        ‖toHilbert (assignment 0).1 + toHilbert (assignment 1).1‖ ^ 2 +
          ‖toHilbert (assignment 0).1 - toHilbert (assignment 1).1‖ ^ 2 :=
      hscaled _ _ _ (ne_of_gt (rationalBallMetricBound_pos (r + r)))
    _ = 2 * (‖toHilbert (assignment 0).1‖ ^ 2 +
          ‖toHilbert (assignment 1).1‖ ^ 2) := hpar
    _ = 2 * rationalBallMetricBound r ^ 2 *
          ((‖toHilbert (assignment 0).1‖ /
              rationalBallMetricBound r) ^ 2 +
            (‖toHilbert (assignment 1).1‖ /
              rationalBallMetricBound r) ^ 2) :=
      (hscaledTwo _ _ _
        (ne_of_gt (rationalBallMetricBound_pos r))).symm

/-- The universal typed parallelogram sentence has value zero on every
rational ball, including the zero-radius sort. -/
@[simp]
theorem parallelogramSentence_value (r : ℚ≥0) :
    (parallelogramSentence r).value expansionStructure = zeroTruthValue := by
  change (⨆ y : expansionStructure.Ball r,
      ⨆ x : expansionStructure.Ball r,
        (parallelogramDiscrepancyFormula r).realize expansionStructure
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) =
    zeroTruthValue
  apply le_antisymm
  · refine iSup_le fun y ↦ iSup_le fun x ↦ ?_
    exact (parallelogramDiscrepancyFormula_realize r
      (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))).le
  · exact ((⨆ y : expansionStructure.Ball r,
      ⨆ x : expansionStructure.Ball r,
        (parallelogramDiscrepancyFormula r).realize expansionStructure
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) :
      TruthValue).2.1

set_option maxHeartbeats 800000 in
/-- The analytic midpoint estimate makes every typed pointwise violation on
the concrete unit ball vanish. -/
theorem midpointViolationFormula_realize
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![(1 : ℚ≥0), (1 : ℚ≥0)] : BallContext 2)) :
    midpointViolationFormula.realize expansionStructure assignment =
      zeroTruthValue := by
  apply (midpointViolationConnective_eq_zero_iff _).2
  simp only [show (![ambientAddUnitFormula, ambientSubUnitFormula]
      (0 : Fin 2)) = ambientAddUnitFormula from rfl,
    show (![ambientAddUnitFormula, ambientSubUnitFormula]
      (1 : Fin 2)) = ambientSubUnitFormula from rfl]
  rw [ambientAddUnitFormula_value, ambientSubUnitFormula_value]
  have hx : ‖(assignment 0).1‖ ≤ 1 := by
    simpa using (assignment 0).2
  have hy : ‖(assignment 1).1‖ ≤ 1 := by
    simpa using (assignment 1).2
  have hmid := norm_midpoint_sq_le (x := (assignment 0).1)
    (y := (assignment 1).1) hx hy
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hmid
  norm_num [rationalBallMetricBound]
  nlinarith

/-- The universal typed midpoint sentence has value zero in the
distinguished expansion. -/
@[simp]
theorem midpointSentence_value :
    midpointSentence.value expansionStructure = zeroTruthValue := by
  change (⨆ y : expansionStructure.Ball (1 : ℚ≥0),
      ⨆ x : expansionStructure.Ball (1 : ℚ≥0),
        midpointViolationFormula.realize expansionStructure
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) =
    zeroTruthValue
  apply le_antisymm
  · refine iSup_le fun y ↦ iSup_le fun x ↦ ?_
    exact (midpointViolationFormula_realize
      (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))).le
  · exact ((⨆ y : expansionStructure.Ball (1 : ℚ≥0),
      ⨆ x : expansionStructure.Ball (1 : ℚ≥0),
        midpointViolationFormula.realize expansionStructure
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) :
      TruthValue).2.1

/-- Equality of complete typed theories transfers the auxiliary-Hilbert
parallelogram identity pointwise on every rational ball. -/
theorem parallelogram_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    (r : ℚ≥0) (x y : M.Ball r) :
    rationalBallMetricBound (r + r) ^ 2 *
        (((hilbertAddFormula r).realize M
            (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) : ℝ) ^ 2 +
          ((hilbertSubFormula r).realize M
            (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) : ℝ) ^ 2) =
      2 * rationalBallMetricBound r ^ 2 *
        (((hilbertFirstFormula r).realize M
            (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) : ℝ) ^ 2 +
          ((hilbertSecondFormula r).realize M
            (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) : ℝ) ^ 2) := by
  have hsentence : (parallelogramSentence r).value M =
      zeroTruthValue := by
    calc
      (parallelogramSentence r).value M =
          (parallelogramSentence r).value expansionStructure :=
        (hTheory (parallelogramSentence r)).symm
      _ = zeroTruthValue := parallelogramSentence_value r
  have hle := realize_le_universalBinarySentence M r
    (parallelogramDiscrepancyFormula r) x y
  change (parallelogramDiscrepancyFormula r).realize M _ ≤
    (parallelogramSentence r).value M at hle
  rw [hsentence] at hle
  have hzero : (parallelogramDiscrepancyFormula r).realize M
      (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) =
        zeroTruthValue :=
    le_antisymm hle
      ((parallelogramDiscrepancyFormula r).realize M
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))).2.1
  simpa using
    (parallelogramDiscrepancyConnective_eq_zero_iff r _).1 hzero

/-- Equality of complete typed theories transfers the fixed midpoint estimate
pointwise on the unit ball. -/
theorem midpoint_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    (x y : M.Ball (1 : ℚ≥0)) :
    4 * (ambientAddUnitFormula.realize M
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) : ℝ) ^ 2 +
      (4 / 3 : ℝ) *
        (ambientSubUnitFormula.realize M
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) : ℝ) ^ 2 ≤
      1 := by
  have hsentence : midpointSentence.value M = zeroTruthValue := by
    calc
      midpointSentence.value M = midpointSentence.value expansionStructure :=
        (hTheory midpointSentence).symm
      _ = zeroTruthValue := midpointSentence_value
  have hle := realize_le_universalBinarySentence M 1
    midpointViolationFormula x y
  change midpointViolationFormula.realize M _ ≤
    midpointSentence.value M at hle
  rw [hsentence] at hle
  have hzero : midpointViolationFormula.realize M
      (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) =
        zeroTruthValue :=
    le_antisymm hle
      (midpointViolationFormula.realize M
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))).2.1
  simpa using (midpointViolationConnective_eq_zero_iff _).1 hzero

end

end NormFormula.X.BallLanguage
