import Mathlib.Topology.MetricSpace.Antilipschitz
import NormFormula.ContinuousLogic.XHilbertBallNormAddIP
import NormFormula.Analytic.MidpointUniformConvex

/-!
# Recovering the small ball sorts in an abstract X-theory model

The directed-union reconstruction has canonical maps *from* every rational
ball sort, but upward coherence alone does not say that a vector of small
reconstructed norm has a representative in a small sort.  This file begins
the missing reverse direction with a continuous sentence.  In a standard
Banach ball system, the distance from a point `x` to the unit ball is at most
`max 0 (||x|| - 1)`.  Unlike a discontinuous implication with antecedent
`||x|| <= 1`, this estimate is expressible in continuous logic and forces
distance zero at the closed boundary.
-/

namespace NormFormula.X.BallLanguage

noncomputable section

open scoped NNReal Topology
open NormFormula.ContinuousLogic

universe u

/-- The normalized excess of an ambient norm above one in a target sort.
If the target sort has language scale `B`, this is
`max 0 (ambientNorm / B - 1 / B)`. -/
def unitBallExcessTruth (target : ℚ≥0) (values : Fin 1 → TruthValue) :
    TruthValue := by
  let scale := rationalBallMetricBound target
  refine ⟨max 0 ((values 0 : ℝ) - 1 / scale), le_max_left _ _, ?_⟩
  apply max_le
  · norm_num
  · have hnonneg : 0 ≤ 1 / scale :=
      div_nonneg (by norm_num) (rationalBallMetricBound_pos target).le
    exact (sub_le_self (values 0 : ℝ) hnonneg).trans (values 0).2.2


/-- The normalized unit-ball excess as a unary continuous connective. -/
def unitBallExcessConnective (target : ℚ≥0) : Connective 1 where
  toFun := unitBallExcessTruth target
  continuous_toFun := by
    have hvalue : Continuous fun values : Fin 1 → TruthValue ↦
        (values 0 : ℝ) :=
      continuous_subtype_val.comp (continuous_apply 0)
    exact (continuous_const.max (hvalue.sub continuous_const)).subtype_mk _

/-- The distance, inside a target sort, from its free target point to the
inclusion of a newly quantified unit-sort point. -/
def unitBallApproximationDistanceFormula
    (target : ℚ≥0) (h : (1 : ℚ≥0) ≤ target) :
    BallFormula PredicateSymbol predicateRadius
      (![(1 : ℚ≥0), target] : BallContext 2) :=
  .distance (.inclusion h (.variable 0)) (.variable 1)

/-- The normalized excess above one of the sole target-sort variable. -/
def unitBallExcessFormula (target : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius
      (![target] : BallContext 1) :=
  .connective (unitBallExcessConnective target) ![
    ambientNormFormula (.variable 0)]

/-- Failure of the assertion that the infimal distance to the included unit
sort is at most the normalized excess above one. -/
def unitBallApproximationViolationFormula
    (target : ℚ≥0) (h : (1 : ℚ≥0) ≤ target) :
    BallFormula PredicateSymbol predicateRadius
      (![target] : BallContext 1) :=
  .connective (scaledOrderViolationConnective 1 (by norm_num)) ![
    .iInf 1 (unitBallApproximationDistanceFormula target h),
    unitBallExcessFormula target]

/-- Universal small-sort approximation sentence for one target radius. -/
def unitBallApproximationSentence
    (target : ℚ≥0) (h : (1 : ℚ≥0) ≤ target) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup target (unitBallApproximationViolationFormula target h)

/-- Concrete value of the target-sort distance to an included unit-sort
point. -/
@[simp]
theorem unitBallApproximationDistanceFormula_value
    (target : ℚ≥0) (h : (1 : ℚ≥0) ≤ target)
    (y : expansionStructure.Ball (1 : ℚ≥0))
    (x : expansionStructure.Ball target) :
    ((unitBallApproximationDistanceFormula target h).realize
        expansionStructure
        (Fin.cons y (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) : ℝ) =
      dist y.1 x.1 / rationalBallMetricBound target := by
  rfl

/-- Concrete value of the normalized excess formula. -/
@[simp]
theorem unitBallExcessFormula_value
    (target : ℚ≥0) (x : expansionStructure.Ball target) :
    ((unitBallExcessFormula target).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) : ℝ) =
      max 0 (‖x.1‖ / rationalBallMetricBound target -
        1 / rationalBallMetricBound target) := by
  change max (0 : ℝ)
      (dist x.1 0 / rationalBallMetricBound target -
        1 / rationalBallMetricBound target) = _
  rw [dist_zero_right]

/-- In the concrete X ball expansion, every point's normalized infimal
distance to the included unit ball is at most its normalized excess above
one. -/
theorem unitBallApproximationViolationFormula_realize
    (target : ℚ≥0) (h : (1 : ℚ≥0) ≤ target)
    (x : expansionStructure.Ball target) :
    (unitBallApproximationViolationFormula target h).realize
        expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) = zeroTruthValue := by
  apply (scaledOrderViolationConnective_eq_zero_iff 1 (by norm_num) _).2
  simp only [show (![
      BallFormula.iInf 1 (unitBallApproximationDistanceFormula target h),
      unitBallExcessFormula target] (0 : Fin 2)) =
        BallFormula.iInf 1
          (unitBallApproximationDistanceFormula target h) from rfl,
    show (![
      BallFormula.iInf 1 (unitBallApproximationDistanceFormula target h),
      unitBallExcessFormula target] (1 : Fin 2)) =
        unitBallExcessFormula target from rfl]
  rw [BallFormula.realize_iInf]
  rw [one_mul, unitBallExcessFormula_value]
  by_cases hx : ‖x.1‖ ≤ (1 : ℝ)
  · let y : expansionStructure.Ball (1 : ℚ≥0) :=
      ⟨x.1, by simpa using hx⟩
    apply le_trans (show
      (↑(⨅ z : expansionStructure.Ball (1 : ℚ≥0),
        (unitBallApproximationDistanceFormula target h).realize
          expansionStructure
          (Fin.cons z (Fin.cons x (fun i : Fin 0 ↦ nomatch i)))) : ℝ) ≤
        ((unitBallApproximationDistanceFormula target h).realize
          expansionStructure
          (Fin.cons y (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) : ℝ) by
            exact_mod_cast iInf_le (fun z : expansionStructure.Ball
              (1 : ℚ≥0) ↦
                (unitBallApproximationDistanceFormula target h).realize
                  expansionStructure
                  (Fin.cons z (Fin.cons x
                    (fun i : Fin 0 ↦ nomatch i)))) y)
    rw [unitBallApproximationDistanceFormula_value]
    rw [dist_self, zero_div]
    exact le_max_left _ _
  · have hxpos : 0 < ‖x.1‖ :=
      lt_of_lt_of_le zero_lt_one (lt_of_not_ge hx).le
    let y : expansionStructure.Ball (1 : ℚ≥0) :=
      ⟨(‖x.1‖⁻¹ : ℝ) • x.1, by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos),
          inv_mul_cancel₀ (ne_of_gt hxpos)]
        norm_num⟩
    apply le_trans (show
      (↑(⨅ z : expansionStructure.Ball (1 : ℚ≥0),
        (unitBallApproximationDistanceFormula target h).realize
          expansionStructure
          (Fin.cons z (Fin.cons x (fun i : Fin 0 ↦ nomatch i)))) : ℝ) ≤
        ((unitBallApproximationDistanceFormula target h).realize
          expansionStructure
          (Fin.cons y (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) : ℝ) by
            exact_mod_cast iInf_le (fun z : expansionStructure.Ball
              (1 : ℚ≥0) ↦
                (unitBallApproximationDistanceFormula target h).realize
                  expansionStructure
                  (Fin.cons z (Fin.cons x
                    (fun i : Fin 0 ↦ nomatch i)))) y)
    rw [unitBallApproximationDistanceFormula_value]
    rw [dist_eq_norm]
    have hcoefficient : 0 ≤ 1 - ‖x.1‖⁻¹ := by
      rw [sub_nonneg, inv_le_one₀ hxpos]
      exact (lt_of_not_ge hx).le
    have hdistance : ‖(‖x.1‖⁻¹ : ℝ) • x.1 - x.1‖ = ‖x.1‖ - 1 := by
      have hv : (‖x.1‖⁻¹ : ℝ) • x.1 - x.1 =
          (‖x.1‖⁻¹ - 1 : ℝ) • x.1 := by
        module
      rw [hv, norm_smul, Real.norm_eq_abs]
      rw [abs_of_nonpos (sub_nonpos.mpr
        ((inv_le_one₀ hxpos).2 (lt_of_not_ge hx).le))]
      field_simp [ne_of_gt hxpos]
      ring
    rw [hdistance, max_eq_right]
    · ring_nf
      rfl
    · rw [sub_nonneg]
      exact div_le_div_of_nonneg_right (lt_of_not_ge hx).le
        (rationalBallMetricBound_pos target).le

/-- The small-sort approximation sentence has value zero in the concrete X
expansion. -/
@[simp]
theorem unitBallApproximationSentence_value
    (target : ℚ≥0) (h : (1 : ℚ≥0) ≤ target) :
    (unitBallApproximationSentence target h).value expansionStructure =
      zeroTruthValue := by
  change (⨆ x : expansionStructure.Ball target,
      (unitBallApproximationViolationFormula target h).realize
        expansionStructure (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) =
    zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun x ↦
      (unitBallApproximationViolationFormula_realize target h x).le
  · exact ((⨆ x : expansionStructure.Ball target,
      (unitBallApproximationViolationFormula target h).realize
        expansionStructure
          (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) : TruthValue).2.1

/-- The transferred sentence gives its pointwise infimal-distance estimate in
every model of the same complete typed theory. -/
theorem unitBallApproximation_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    (target : ℚ≥0) (h : (1 : ℚ≥0) ≤ target)
    (x : M.Ball target) :
    ((BallFormula.iInf 1
        (unitBallApproximationDistanceFormula target h)).realize M
          (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) : ℝ) ≤
      ((unitBallExcessFormula target).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) : ℝ) := by
  have hsentence :
      (unitBallApproximationSentence target h).value M = zeroTruthValue := by
    calc
      (unitBallApproximationSentence target h).value M =
          (unitBallApproximationSentence target h).value expansionStructure :=
        (hTheory (unitBallApproximationSentence target h)).symm
      _ = zeroTruthValue := unitBallApproximationSentence_value target h
  have hle := realize_le_unarySentence M target
    (unitBallApproximationViolationFormula target h) x
  change (unitBallApproximationViolationFormula target h).realize M _ ≤
    (unitBallApproximationSentence target h).value M at hle
  rw [hsentence] at hle
  have hzero :
      (unitBallApproximationViolationFormula target h).realize M
          (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) = zeroTruthValue :=
    le_antisymm hle
      ((unitBallApproximationViolationFormula target h).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).2.1
  have horder :=
    (scaledOrderViolationConnective_eq_zero_iff 1 (by norm_num) _).1 hzero
  simpa only [unitBallApproximationViolationFormula,
    BallFormula.realize_connective,
    show (![
      BallFormula.iInf 1 (unitBallApproximationDistanceFormula target h),
      unitBallExcessFormula target] (0 : Fin 2)) =
        BallFormula.iInf 1
          (unitBallApproximationDistanceFormula target h) from rfl,
    show (![
      BallFormula.iInf 1 (unitBallApproximationDistanceFormula target h),
      unitBallExcessFormula target] (1 : Fin 2)) =
        unitBallExcessFormula target from rfl,
    one_mul] using horder

/-- A target-sort point's ambient norm formula is exactly its reconstructed
norm divided by the target language scale. -/
theorem ambientNormVariable_completedNorm
    (A : XBallTheoryModel.{u}) (target : ℚ≥0)
    (x : A.model.Ball target) :
    ‖A.ballToCompletedDirectedPoint target x‖ =
      rationalBallMetricBound target *
        ((ambientNormFormula (unaryVariable target)).realize A.model
          (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) : ℝ) := by
  rw [A.norm_completedDirectedPoint, dist_comm,
    ← A.ballToCompletedDirectedPoint_zero target,
    A.dist_ballToCompletedDirectedPoint]
  rfl

/-- Semantic value of the excess formula in the reconstructed norm. -/
theorem unitBallExcessFormula_completedValue
    (A : XBallTheoryModel.{u}) (target : ℚ≥0)
    (x : A.model.Ball target) :
    ((unitBallExcessFormula target).realize A.model
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) : ℝ) =
      max 0 (‖A.ballToCompletedDirectedPoint target x‖ /
          rationalBallMetricBound target -
        1 / rationalBallMetricBound target) := by
  change max (0 : ℝ)
      (((ambientNormFormula (unaryVariable target)).realize A.model
          (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) : ℝ) -
        1 / rationalBallMetricBound target) = _
  rw [ambientNormVariable_completedNorm]
  congr 2
  field_simp [ne_of_gt (rationalBallMetricBound_pos target)]

/-- The small-sort distance formula is exactly reconstructed distance divided
by the target language scale. -/
theorem unitBallApproximationDistanceFormula_completedDistance
    (A : XBallTheoryModel.{u})
    (target : ℚ≥0) (h : (1 : ℚ≥0) ≤ target)
    (y : A.model.Ball 1) (x : A.model.Ball target) :
    dist (A.ballToCompletedDirectedPoint 1 y)
        (A.ballToCompletedDirectedPoint target x) =
      rationalBallMetricBound target *
        ((unitBallApproximationDistanceFormula target h).realize A.model
          (Fin.cons y (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) : ℝ) := by
  rw [← A.ballToCompletedDirectedPoint_inclusion h y,
    A.dist_ballToCompletedDirectedPoint]
  rfl

/-- Lipschitz constant of one canonical typed-sort map into the reconstructed
completion. -/
def ballToCompletedDirectedPointLipschitzConstant
    (A : XBallTheoryModel.{u}) (radius : ℚ≥0) : ℝ≥0 :=
  ⟨rationalBallMetricBound radius / A.model.sortBound radius,
    div_nonneg (rationalBallMetricBound_pos radius).le
      (A.model.sortBound_pos radius).le⟩

/-- Antilipschitz constant of one canonical typed-sort map into the
reconstructed completion. -/
def ballToCompletedDirectedPointAntilipschitzConstant
    (A : XBallTheoryModel.{u}) (radius : ℚ≥0) : ℝ≥0 :=
  ⟨A.model.sortBound radius / rationalBallMetricBound radius,
    div_nonneg (A.model.sortBound_pos radius).le
      (rationalBallMetricBound_pos radius).le⟩

/-- Every canonical typed-sort map is quantitatively Lipschitz. -/
theorem ballToCompletedDirectedPoint_lipschitzWith
    (A : XBallTheoryModel.{u}) (radius : ℚ≥0) :
    LipschitzWith (ballToCompletedDirectedPointLipschitzConstant A radius)
      (A.ballToCompletedDirectedPoint radius) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [A.dist_ballToCompletedDirectedPoint]
  change rationalBallMetricBound radius *
      (dist x y / A.model.sortBound radius) ≤
    (rationalBallMetricBound radius / A.model.sortBound radius) * dist x y
  ring_nf
  exact le_rfl

/-- Every canonical typed-sort map is quantitatively antilipschitz.  The
domain may be a pseudometric sort; injectivity is neither asserted nor needed
for closedness of its range in the metric completion. -/
theorem ballToCompletedDirectedPoint_antilipschitzWith
    (A : XBallTheoryModel.{u}) (radius : ℚ≥0) :
    AntilipschitzWith
      (ballToCompletedDirectedPointAntilipschitzConstant A radius)
      (A.ballToCompletedDirectedPoint radius) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  rw [A.dist_ballToCompletedDirectedPoint]
  change dist x y ≤
    (A.model.sortBound radius / rationalBallMetricBound radius) *
      (rationalBallMetricBound radius *
        (dist x y / A.model.sortBound radius))
  field_simp [ne_of_gt (A.model.sortBound_pos radius),
    ne_of_gt (rationalBallMetricBound_pos radius)]
  exact le_rfl

/-- Completeness of a typed sort and its exact two-sided distance scaling make
the range of its canonical map closed in the reconstructed completion. -/
theorem ballToCompletedDirectedPoint_range_isClosed
    (A : XBallTheoryModel.{u}) (radius : ℚ≥0) :
    IsClosed (Set.range (A.ballToCompletedDirectedPoint radius)) :=
  (ballToCompletedDirectedPoint_antilipschitzWith A radius).isClosed_range
    (ballToCompletedDirectedPoint_lipschitzWith A radius).uniformContinuous

/-- Every canonical point of reconstructed norm at most one, regardless of
the sort in which it is initially represented, is approximated arbitrarily
well by canonical points from the typed unit sort. -/
theorem exists_unitBall_completedDistance_lt
    (A : XBallTheoryModel.{u})
    (target : ℚ≥0) (h : (1 : ℚ≥0) ≤ target)
    (x : A.model.Ball target)
    (hx : ‖A.ballToCompletedDirectedPoint target x‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : A.model.Ball 1,
      dist (A.ballToCompletedDirectedPoint 1 y)
        (A.ballToCompletedDirectedPoint target x) < ε := by
  have hinf := unitBallApproximation_of_sameCompleteTheory A.model
    A.sameCompleteTheory target h x
  rw [unitBallExcessFormula_completedValue] at hinf
  have hexcess : max 0
      (‖A.ballToCompletedDirectedPoint target x‖ /
          rationalBallMetricBound target -
        1 / rationalBallMetricBound target) = 0 := by
    apply max_eq_left
    rw [sub_nonpos]
    exact div_le_div_of_nonneg_right hx
      (rationalBallMetricBound_pos target).le
  rw [hexcess] at hinf
  have hinfZero :
      (BallFormula.iInf 1
        (unitBallApproximationDistanceFormula target h)).realize A.model
          (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) = zeroTruthValue := by
    apply le_antisymm
    · exact_mod_cast hinf
    · exact ((BallFormula.iInf 1
        (unitBallApproximationDistanceFormula target h)).realize A.model
          (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).2.1
  have hscaledε : 0 < ε / rationalBallMetricBound target :=
    div_pos hε (rationalBallMetricBound_pos target)
  obtain ⟨y, hy⟩ := BallFormula.exists_iInf_approximation 1
    (unitBallApproximationDistanceFormula target h) A.model
    (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) hscaledε
  refine ⟨y, ?_⟩
  rw [hinfZero, zeroTruthValue_coe, zero_add] at hy
  rw [unitBallApproximationDistanceFormula_completedDistance A target h]
  calc
    rationalBallMetricBound target *
          ((unitBallApproximationDistanceFormula target h).realize A.model
            (Fin.cons y (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) : ℝ) <
        rationalBallMetricBound target *
          (ε / rationalBallMetricBound target) :=
      mul_lt_mul_of_pos_left hy (rationalBallMetricBound_pos target)
    _ = ε := by
      field_simp [ne_of_gt (rationalBallMetricBound_pos target)]

/-- Reverse small-sort representation for canonical points: if a point first
presented in any radius at least one has reconstructed norm at most one, then
it is exactly the image of a point in the typed unit sort. -/
theorem exists_unitBall_eq_of_completedNorm_le_one
    (A : XBallTheoryModel.{u})
    (target : ℚ≥0) (h : (1 : ℚ≥0) ≤ target)
    (x : A.model.Ball target)
    (hx : ‖A.ballToCompletedDirectedPoint target x‖ ≤ 1) :
    ∃ y : A.model.Ball 1,
      A.ballToCompletedDirectedPoint 1 y =
        A.ballToCompletedDirectedPoint target x := by
  let point := A.ballToCompletedDirectedPoint target x
  have hclosure : point ∈
      closure (Set.range (A.ballToCompletedDirectedPoint 1)) := by
    apply Metric.mem_closure_iff.2
    intro ε hε
    obtain ⟨y, hy⟩ := exists_unitBall_completedDistance_lt A target h x hx hε
    exact ⟨A.ballToCompletedDirectedPoint 1 y, ⟨y, rfl⟩,
      by simpa only [point, dist_comm] using hy⟩
  have hrange : point ∈
      Set.range (A.ballToCompletedDirectedPoint 1) := by
    rw [← (ballToCompletedDirectedPoint_range_isClosed A 1).closure_eq]
    exact hclosure
  obtain ⟨y, hy⟩ := hrange
  exact ⟨y, hy⟩

/-- Every canonical reconstructed point of norm at most one has an exact
representative in the typed unit sort, irrespective of its original radius. -/
theorem exists_unitBall_eq_of_completedNorm_le_one_anyRadius
    (A : XBallTheoryModel.{u})
    (radius : ℚ≥0) (x : A.model.Ball radius)
    (hx : ‖A.ballToCompletedDirectedPoint radius x‖ ≤ 1) :
    ∃ y : A.model.Ball 1,
      A.ballToCompletedDirectedPoint 1 y =
        A.ballToCompletedDirectedPoint radius x := by
  rcases le_total radius (1 : ℚ≥0) with hradius | hradius
  · exact ⟨A.model.inclusion hradius x,
      A.ballToCompletedDirectedPoint_inclusion hradius x⟩
  · exact exists_unitBall_eq_of_completedNorm_le_one
      A radius hradius x hx

/-- A rational multiple of a point in the canonical dense image is again a
canonical typed-sort point.  Consequently, if that multiple has completed
norm at most one, it already has an exact representative in the typed unit
sort. -/
theorem exists_unitBall_eq_rationalSmul_toCompletedDirectedPoint
    (A : XBallTheoryModel.{u})
    (q : ℚ) (z : A.SeparatedDirectedPoint)
    (hz : ‖q • A.toCompletedDirectedPoint z‖ ≤ 1) :
    ∃ y : A.model.Ball 1,
      A.ballToCompletedDirectedPoint 1 y =
        q • A.toCompletedDirectedPoint z := by
  revert hz
  refine Quotient.inductionOn' z ?_
  rintro ⟨radius, x⟩ hz
  change ‖q • A.ballToCompletedDirectedPoint radius x‖ ≤ 1 at hz
  change ∃ y : A.model.Ball 1,
    A.ballToCompletedDirectedPoint 1 y =
      q • A.ballToCompletedDirectedPoint radius x
  rw [← A.ballToCompletedDirectedPoint_smul q radius x] at hz ⊢
  exact exists_unitBall_eq_of_completedNorm_le_one_anyRadius A
    (q.nnabs * radius) (A.model.smul q radius x) hz

/-- Every completed vector of norm at most one is approximated arbitrarily
well by the canonical image of the typed unit sort.  Starting from a nearby
point `a` in the dense rational directed union, the proof replaces `a` by
`q • a`, where `q = 1 / (1 + t)` and `t` bounds the approximation error.
This guarantees both `‖q • a‖ < 1` and `dist a (q • a) < t`. -/
theorem exists_unitBall_completedDistance_lt_of_completedNorm_le_one
    (A : XBallTheoryModel.{u})
    (p : A.CompletedDirectedPoint) (hp : ‖p‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : A.model.Ball 1,
      dist (A.ballToCompletedDirectedPoint 1 y) p < ε := by
  obtain ⟨t, ht, htε⟩ := exists_pos_rat_lt (half_pos hε)
  let q : ℚ := 1 / (1 + t)
  have htden : 0 < (1 + t : ℚ) := by linarith
  have hq : 0 < q := by
    dsimp [q]
    exact div_pos zero_lt_one htden
  have hq_lt_one : q < 1 := by
    dsimp [q]
    rw [div_lt_one htden]
    linarith
  have hdelta : 0 < (1 - q : ℚ) := sub_pos.mpr hq_lt_one
  have hq_mul_rat : q * (1 + t) = 1 := by
    dsimp [q]
    field_simp [ne_of_gt htden]
  have hdelta_mul_rat : (1 - q) * (1 + t) = t := by
    rw [sub_mul, hq_mul_rat, one_mul]
    ring
  have hq_mul_real : (q : ℝ) * (1 + (t : ℝ)) = 1 := by
    exact_mod_cast hq_mul_rat
  have hdelta_mul_real : ((1 - q : ℚ) : ℝ) *
      (1 + (t : ℝ)) = t := by
    exact_mod_cast hdelta_mul_rat
  obtain ⟨z, hz⟩ := Metric.denseRange_iff.mp
    A.denseRange_toCompletedDirectedPoint p (t : ℝ) (by exact_mod_cast ht)
  let a := A.toCompletedDirectedPoint z
  have hpa : dist p a < (t : ℝ) := by
    exact hz
  have hapNorm : ‖a - p‖ < (t : ℝ) := by
    rw [← dist_eq_norm, dist_comm]
    exact hpa
  have ha : ‖a‖ < 1 + (t : ℝ) := by
    calc
      ‖a‖ = ‖p + (a - p)‖ := by
        congr 1
        abel
      _ ≤ ‖p‖ + ‖a - p‖ := norm_add_le p (a - p)
      _ ≤ 1 + ‖a - p‖ := add_le_add hp le_rfl
      _ < 1 + (t : ℝ) := by linarith
  have hscaled : ‖q • a‖ ≤ 1 := by
    apply le_of_lt
    calc
      ‖q • a‖ = ‖q‖ * ‖a‖ := A.norm_completedSmul q a
      _ = (q : ℝ) * ‖a‖ := by
        rw [← Rat.norm_cast_real, Real.norm_eq_abs,
          abs_of_pos (by exact_mod_cast hq : (0 : ℝ) < q)]
      _ < (q : ℝ) * (1 + (t : ℝ)) :=
        mul_lt_mul_of_pos_left ha (by exact_mod_cast hq)
      _ = 1 := hq_mul_real
  have hascaleDistance : dist a (q • a) < (t : ℝ) := by
    calc
      dist a (q • a) = ‖a - q • a‖ := by rw [dist_eq_norm]
      _ = ‖(1 - q) • a‖ := by rw [sub_smul, one_smul]
      _ = ‖1 - q‖ * ‖a‖ := A.norm_completedSmul (1 - q) a
      _ = ((1 - q : ℚ) : ℝ) * ‖a‖ := by
        rw [← Rat.norm_cast_real, Real.norm_eq_abs,
          abs_of_pos (by exact_mod_cast hdelta : (0 : ℝ) < (1 - q : ℚ))]
      _ < ((1 - q : ℚ) : ℝ) * (1 + (t : ℝ)) :=
        mul_lt_mul_of_pos_left ha (by exact_mod_cast hdelta)
      _ = t := hdelta_mul_real
  obtain ⟨y, hy⟩ :=
    exists_unitBall_eq_rationalSmul_toCompletedDirectedPoint A q z hscaled
  refine ⟨y, ?_⟩
  rw [hy]
  calc
    dist (q • a) p = dist p (q • a) := dist_comm _ _
    _ ≤ dist p a + dist a (q • a) := dist_triangle p a (q • a)
    _ < (t : ℝ) + t := add_lt_add hpa hascaleDistance
    _ < ε := by linarith

/-- The typed unit sort maps exactly onto the closed unit ball of the
reconstructed completion. -/
theorem exists_unitBall_eq_of_completedNorm_le_one_global
    (A : XBallTheoryModel.{u})
    (p : A.CompletedDirectedPoint) (hp : ‖p‖ ≤ 1) :
    ∃ y : A.model.Ball 1,
      A.ballToCompletedDirectedPoint 1 y = p := by
  have hclosure : p ∈
      closure (Set.range (A.ballToCompletedDirectedPoint 1)) := by
    apply Metric.mem_closure_iff.2
    intro ε hε
    obtain ⟨y, hy⟩ :=
      exists_unitBall_completedDistance_lt_of_completedNorm_le_one A p hp hε
    exact ⟨A.ballToCompletedDirectedPoint 1 y, ⟨y, rfl⟩,
      by simpa only [dist_comm] using hy⟩
  have hrange : p ∈ Set.range (A.ballToCompletedDirectedPoint 1) := by
    rw [← (ballToCompletedDirectedPoint_range_isClosed A 1).closure_eq]
    exact hclosure
  exact hrange

/-- The syntax-transferred quadratic midpoint estimate holds on the entire
closed unit ball of the reconstructed completion, not merely on canonical
points already presented in the typed unit sort. -/
theorem midpoint_completedNorm
    (A : XBallTheoryModel.{u})
    (x y : A.CompletedDirectedPoint)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤
      1 - (1 / 12 : ℝ) * ‖x - y‖ ^ 2 := by
  obtain ⟨x', hx'⟩ :=
    exists_unitBall_eq_of_completedNorm_le_one_global A x hx
  obtain ⟨y', hy'⟩ :=
    exists_unitBall_eq_of_completedNorm_le_one_global A y hy
  simpa only [hx', hy'] using midpoint_completedNorm_of_typedUnit A x' y'

/-- The reconstructed completion of every model of the complete X ball
theory is uniformly convex, with the explicit modulus extracted from the
paper's `1/12` midpoint estimate. -/
@[reducible] noncomputable def completedDirectedPointUniformConvexSpace
    (A : XBallTheoryModel.{u}) :
    UniformConvexSpace A.CompletedDirectedPoint :=
  NormFormula.uniformConvexSpaceOfMidpointEstimate (midpoint_completedNorm A)

end

end NormFormula.X.BallLanguage
