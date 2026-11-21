import Mathlib.Tactic.DeriveEncodable
import NormFormula.Analytic.XHilbertEquiv
import NormFormula.ContinuousLogic.BanachBallFormula
import NormFormula.ContinuousLogic.ScaledOrderViolation

/-!
# The ball-sorted auxiliary Hilbert expansion of `X`

For every nonnegative rational radius, the standard Banach ball system of
`XSpace` is expanded by its auxiliary Hilbert norm, normalized by the positive
metric bound of that sort.  Typed distance to the actual zero term supplies
the ambient norm.  The two comparison inequalities are then genuine
ball-sorted universal sentences and transfer to every model of the same
complete typed theory.
-/

namespace NormFormula.X.BallLanguage

noncomputable section

open scoped Topology
open NormFormula.ContinuousLogic

universe u

/-- One auxiliary Hilbert predicate for each rational ball sort. -/
inductive PredicateSymbol
  | hilbert (radius : ℚ≥0)
  deriving DecidableEq, Encodable

/-- The sort on which an auxiliary Hilbert predicate is interpreted. -/
def predicateRadius : PredicateSymbol → ℚ≥0
  | .hilbert radius => radius

/-- The normalized auxiliary Hilbert norm on one rational ball. -/
def hilbertNormTruth (r : ℚ≥0) (x : RationalNormBall XSpace r) :
    TruthValue := by
  refine ⟨‖toHilbert x.1‖ / rationalBallMetricBound r,
    div_nonneg (norm_nonneg _) (rationalBallMetricBound_pos r).le, ?_⟩
  apply (div_le_one (rationalBallMetricBound_pos r)).2
  calc
    ‖toHilbert x.1‖ ≤ ‖x.1‖ := norm_toHilbert_le x.1
    _ ≤ (r : ℝ) := x.2
    _ ≤ 2 * (r : ℝ) := by
      have hr : 0 ≤ (r : ℝ) := by positivity
      linarith
    _ ≤ max 1 (2 * (r : ℝ)) := le_max_right _ _

@[simp]
theorem hilbertNormTruth_coe (r : ℚ≥0) (x : RationalNormBall XSpace r) :
    (hilbertNormTruth r x : ℝ) =
      ‖toHilbert x.1‖ / rationalBallMetricBound r :=
  rfl

/-- Uniform continuity of the normalized auxiliary Hilbert predicate. -/
theorem hilbertNormTruth_uniformContinuous (r : ℚ≥0) :
    UniformContinuous (hilbertNormTruth r) := by
  have hmap : UniformContinuous
      (fun x : RationalNormBall XSpace r ↦ toHilbert x.1) :=
    continuousLinearEquivHilbertSum.toContinuousLinearMap.uniformContinuous.comp
      uniformContinuous_subtype_val
  exact ((uniformContinuous_norm.comp hmap).div_const'
    (rationalBallMetricBound r)).subtype_mk _

/-- The standard rational-ball Banach structure of `XSpace`, expanded by its
auxiliary Hilbert norm on every sort. -/
def expansionStructure : BallStructure PredicateSymbol predicateRadius where
  toRationalBallSystem := standardRationalBallSystem (E := XSpace)
  predicate
    | .hilbert radius => hilbertNormTruth radius
  predicate_uniformContinuous
    | .hilbert radius => hilbertNormTruth_uniformContinuous radius

/-- Ambient norm of a typed term, expressed as normalized distance to the
actual zero term of its output sort. -/
def ambientNormFormula {n : ℕ} {context : BallContext n} {r : ℚ≥0}
    (term : BallTerm context r) :
    BallFormula PredicateSymbol predicateRadius context :=
  .distance term (.zero r)

/-- Auxiliary Hilbert norm of a typed term. -/
def hilbertNormFormula {n : ℕ} {context : BallContext n} {r : ℚ≥0}
    (term : BallTerm context r) :
    BallFormula PredicateSymbol predicateRadius context :=
  .predicate (.hilbert r) term

/-- Failure of `h(t) ≤ ‖t‖` for a typed term. -/
def hilbertLeAmbientViolationFormula
    {n : ℕ} {context : BallContext n} {r : ℚ≥0}
    (term : BallTerm context r) :
    BallFormula PredicateSymbol predicateRadius context :=
  .connective (scaledOrderViolationConnective 1 (by norm_num))
    ![hilbertNormFormula term, ambientNormFormula term]

/-- Failure of `‖t‖ ≤ √3 h(t)` for a typed term. -/
def ambientLeSqrtThreeHilbertViolationFormula
    {n : ℕ} {context : BallContext n} {r : ℚ≥0}
    (term : BallTerm context r) :
    BallFormula PredicateSymbol predicateRadius context :=
  .connective
    (scaledOrderViolationConnective (Real.sqrt 3) (Real.sqrt_nonneg 3))
    ![ambientNormFormula term, hilbertNormFormula term]

/-- The sole variable in a one-variable radius-`r` context. -/
def unaryVariable (r : ℚ≥0) : BallTerm (![r] : BallContext 1) r :=
  .variable 0

/-- Universal lower-comparison sentence on the radius-`r` sort. -/
def hilbertLeAmbientSentence (r : ℚ≥0) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup r (hilbertLeAmbientViolationFormula (unaryVariable r))

/-- Universal upper-comparison sentence on the radius-`r` sort. -/
def ambientLeSqrtThreeHilbertSentence (r : ℚ≥0) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup r (ambientLeSqrtThreeHilbertViolationFormula (unaryVariable r))

/-- Concrete evaluation of the ambient norm formula. -/
theorem ambientNormFormula_value
    {n : ℕ} {context : BallContext n} {r : ℚ≥0}
    (term : BallTerm context r)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem context) :
    ((ambientNormFormula term).realize expansionStructure assignment : ℝ) =
      ‖term.standardValue assignment‖ / rationalBallMetricBound r := by
  change dist
      (term.realize expansionStructure.toRationalBallSystem assignment)
      (rationalBallZero (E := XSpace) r) /
      rationalBallMetricBound r = _
  simp only [expansionStructure]
  change dist (term.standardValue assignment) 0 /
      rationalBallMetricBound r = _
  rw [dist_zero_right]

/-- Concrete evaluation of the auxiliary Hilbert norm formula. -/
theorem hilbertNormFormula_value
    {n : ℕ} {context : BallContext n} {r : ℚ≥0}
    (term : BallTerm context r)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem context) :
    ((hilbertNormFormula term).realize expansionStructure assignment : ℝ) =
      ‖toHilbert (term.standardValue assignment)‖ /
        rationalBallMetricBound r :=
  rfl

/-- Both comparison violations vanish pointwise in the distinguished typed
expansion. -/
theorem comparisonViolationFormulae_realize
    {n : ℕ} {context : BallContext n} {r : ℚ≥0}
    (term : BallTerm context r)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem context) :
    (hilbertLeAmbientViolationFormula term).realize
        expansionStructure assignment = zeroTruthValue ∧
      (ambientLeSqrtThreeHilbertViolationFormula term).realize
        expansionStructure assignment = zeroTruthValue := by
  constructor
  · apply (scaledOrderViolationConnective_eq_zero_iff 1 (by norm_num) _).2
    simp only [show (![hilbertNormFormula term, ambientNormFormula term]
        (0 : Fin 2)) = hilbertNormFormula term from rfl,
      show (![hilbertNormFormula term, ambientNormFormula term]
        (1 : Fin 2)) = ambientNormFormula term from rfl]
    rw [hilbertNormFormula_value, ambientNormFormula_value]
    simpa using div_le_div_of_nonneg_right
      (norm_toHilbert_le (term.standardValue assignment))
      (rationalBallMetricBound_pos r).le
  · apply (scaledOrderViolationConnective_eq_zero_iff
      (Real.sqrt 3) (Real.sqrt_nonneg 3) _).2
    simp only [show (![ambientNormFormula term, hilbertNormFormula term]
        (0 : Fin 2)) = ambientNormFormula term from rfl,
      show (![ambientNormFormula term, hilbertNormFormula term]
        (1 : Fin 2)) = hilbertNormFormula term from rfl]
    rw [hilbertNormFormula_value, ambientNormFormula_value]
    have hcomparison := norm_ofHilbert_le
      (toHilbert (term.standardValue assignment))
    have hnorm : ‖term.standardValue assignment‖ ≤
        Real.sqrt 3 * ‖toHilbert (term.standardValue assignment)‖ := by
      simpa using hcomparison
    calc
      ‖term.standardValue assignment‖ / rationalBallMetricBound r ≤
          (Real.sqrt 3 * ‖toHilbert (term.standardValue assignment)‖) /
            rationalBallMetricBound r :=
        div_le_div_of_nonneg_right hnorm
          (rationalBallMetricBound_pos r).le
      _ = Real.sqrt 3 *
          (‖toHilbert (term.standardValue assignment)‖ /
            rationalBallMetricBound r) := by ring

/-- The lower-comparison sentence has value zero in the distinguished
expansion. -/
@[simp]
theorem hilbertLeAmbientSentence_value (r : ℚ≥0) :
    (hilbertLeAmbientSentence r).value expansionStructure = zeroTruthValue := by
  change (⨆ x : expansionStructure.Ball r,
      (hilbertLeAmbientViolationFormula (unaryVariable r)).realize
        expansionStructure (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) =
    zeroTruthValue
  apply le_antisymm
  · refine iSup_le fun x ↦ ?_
    exact (comparisonViolationFormulae_realize (unaryVariable r)
      (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).1.le
  · exact ((⨆ x : expansionStructure.Ball r,
      (hilbertLeAmbientViolationFormula (unaryVariable r)).realize
        expansionStructure (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) :
      TruthValue).2.1

/-- The upper-comparison sentence has value zero in the distinguished
expansion. -/
@[simp]
theorem ambientLeSqrtThreeHilbertSentence_value (r : ℚ≥0) :
    (ambientLeSqrtThreeHilbertSentence r).value expansionStructure =
      zeroTruthValue := by
  change (⨆ x : expansionStructure.Ball r,
      (ambientLeSqrtThreeHilbertViolationFormula (unaryVariable r)).realize
        expansionStructure (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) =
    zeroTruthValue
  apply le_antisymm
  · refine iSup_le fun x ↦ ?_
    exact (comparisonViolationFormulae_realize (unaryVariable r)
      (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).2.le
  · exact ((⨆ x : expansionStructure.Ball r,
      (ambientLeSqrtThreeHilbertViolationFormula (unaryVariable r)).realize
        expansionStructure (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) :
      TruthValue).2.1

/-- Every pointwise instance is bounded by its one-sort universal closure. -/
theorem realize_le_unarySentence
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (r : ℚ≥0)
    (formula : BallFormula PredicateSymbol predicateRadius
      (![r] : BallContext 1))
    (x : M.Ball r) :
    formula.realize M (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) ≤
      BallSentence.value
        (BallFormula.iSup r formula :
          BallSentence PredicateSymbol predicateRadius) M := by
  exact le_iSup
    (fun y : M.Ball r ↦
      formula.realize M (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) x

/-- Same complete typed theory transfers both comparison inequalities on
every rational ball sort. -/
theorem comparisons_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    (r : ℚ≥0) (x : M.Ball r) :
    ((hilbertNormFormula (unaryVariable r)).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) : ℝ) ≤
      ((ambientNormFormula (unaryVariable r)).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) : ℝ) ∧
    ((ambientNormFormula (unaryVariable r)).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) : ℝ) ≤
      Real.sqrt 3 *
        ((hilbertNormFormula (unaryVariable r)).realize M
          (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) : ℝ) := by
  have hlowerSentence : (hilbertLeAmbientSentence r).value M =
      zeroTruthValue := by
    calc
      (hilbertLeAmbientSentence r).value M =
          (hilbertLeAmbientSentence r).value expansionStructure :=
        (hTheory (hilbertLeAmbientSentence r)).symm
      _ = zeroTruthValue := hilbertLeAmbientSentence_value r
  have hupperSentence : (ambientLeSqrtThreeHilbertSentence r).value M =
      zeroTruthValue := by
    calc
      (ambientLeSqrtThreeHilbertSentence r).value M =
          (ambientLeSqrtThreeHilbertSentence r).value expansionStructure :=
        (hTheory (ambientLeSqrtThreeHilbertSentence r)).symm
      _ = zeroTruthValue := ambientLeSqrtThreeHilbertSentence_value r
  constructor
  · have hle := realize_le_unarySentence M r
      (hilbertLeAmbientViolationFormula (unaryVariable r)) x
    change _ ≤ (hilbertLeAmbientSentence r).value M at hle
    rw [hlowerSentence] at hle
    have hzero := le_antisymm hle
      ((hilbertLeAmbientViolationFormula (unaryVariable r)).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).2.1
    simpa using
      (scaledOrderViolationConnective_eq_zero_iff 1 (by norm_num) _).1 hzero
  · have hle := realize_le_unarySentence M r
      (ambientLeSqrtThreeHilbertViolationFormula (unaryVariable r)) x
    change _ ≤ (ambientLeSqrtThreeHilbertSentence r).value M at hle
    rw [hupperSentence] at hle
    have hzero := le_antisymm hle
      ((ambientLeSqrtThreeHilbertViolationFormula (unaryVariable r)).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).2.1
    simpa using (scaledOrderViolationConnective_eq_zero_iff
      (Real.sqrt 3) (Real.sqrt_nonneg 3) _).1 hzero

end

end NormFormula.X.BallLanguage
