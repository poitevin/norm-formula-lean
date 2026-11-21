import NormFormula.ContinuousLogic.AbsoluteDifference
import NormFormula.ContinuousLogic.DoublyScaledAbsoluteDifference
import NormFormula.ContinuousLogic.ScaledAbsoluteDifference
import NormFormula.ContinuousLogic.ScaledOrderViolation
import NormFormula.ContinuousLogic.XHilbertBallExpansion

/-!
# Observable coherence laws in the typed X ball theory

The raw `RationalBallSystem` structure supplies interpretations of the
radius inclusions but deliberately does not impose their algebraic laws as
Lean fields.  This file begins the syntax-level reconstruction interface:
the identity and composition laws are expressed by universal distance-zero
sentences, proved in the distinguished X expansion, and transferred to every
model of its complete typed theory.

Because ball sorts are pseudometric spaces, the transferred conclusion is
correctly stated as zero distance.  It becomes literal equality after the
metric-separation quotient used by the eventual one-sorted reduct.
-/

namespace NormFormula.X.BallLanguage

noncomputable section

open NormFormula.ContinuousLogic

universe u

/-- Failure of the identity inclusion law on the radius-`r` sort. -/
def inclusionReflFormula (r : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius
      (![r] : BallContext 1) :=
  .distance
    (.inclusion (le_refl r) (.variable 0))
    (.variable 0)

/-- Universal identity-inclusion sentence at radius `r`. -/
def inclusionReflSentence (r : ℚ≥0) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup r (inclusionReflFormula r)

/-- Failure of functoriality for inclusions `r → s → t`. -/
def inclusionTransFormula {r s t : ℚ≥0}
    (hrs : r ≤ s) (hst : s ≤ t) :
    BallFormula PredicateSymbol predicateRadius
      (![r] : BallContext 1) :=
  .distance
    (.inclusion hst (.inclusion hrs (.variable 0)))
    (.inclusion (hrs.trans hst) (.variable 0))

/-- Universal composition sentence for inclusions `r → s → t`. -/
def inclusionTransSentence {r s t : ℚ≥0}
    (hrs : r ≤ s) (hst : s ≤ t) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup r (inclusionTransFormula hrs hst)

/-- The concrete identity-inclusion formula vanishes pointwise. -/
theorem inclusionReflFormula_realize (r : ℚ≥0)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r] : BallContext 1)) :
    (inclusionReflFormula r).realize expansionStructure assignment =
      zeroTruthValue := by
  apply Subtype.ext
  change dist
      (rationalBallInclusion (E := XSpace) (le_refl r) (assignment 0))
      (assignment 0) / rationalBallMetricBound r = 0
  change dist (assignment 0).1 (assignment 0).1 /
    rationalBallMetricBound r = 0
  simp

/-- The concrete inclusion-composition formula vanishes pointwise. -/
theorem inclusionTransFormula_realize {r s t : ℚ≥0}
    (hrs : r ≤ s) (hst : s ≤ t)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r] : BallContext 1)) :
    (inclusionTransFormula hrs hst).realize expansionStructure assignment =
      zeroTruthValue := by
  apply Subtype.ext
  change dist
      (rationalBallInclusion (E := XSpace) hst
        (rationalBallInclusion (E := XSpace) hrs (assignment 0)))
      (rationalBallInclusion (E := XSpace) (hrs.trans hst) (assignment 0)) /
        rationalBallMetricBound t = 0
  rw [rationalBallInclusion_trans]
  simp

/-- Identity inclusion is a zero-valued sentence of the distinguished X
theory. -/
@[simp]
theorem inclusionReflSentence_value (r : ℚ≥0) :
    (inclusionReflSentence r).value expansionStructure = zeroTruthValue := by
  change (⨆ x : expansionStructure.Ball r,
      (inclusionReflFormula r).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) = zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun x ↦
      (inclusionReflFormula_realize r
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).le
  · exact ((⨆ x : expansionStructure.Ball r,
      (inclusionReflFormula r).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) : TruthValue).2.1

/-- Composition of inclusions is a zero-valued sentence of the distinguished
X theory. -/
@[simp]
theorem inclusionTransSentence_value {r s t : ℚ≥0}
    (hrs : r ≤ s) (hst : s ≤ t) :
    (inclusionTransSentence hrs hst).value expansionStructure =
      zeroTruthValue := by
  change (⨆ x : expansionStructure.Ball r,
      (inclusionTransFormula hrs hst).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) = zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun x ↦
      (inclusionTransFormula_realize hrs hst
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).le
  · exact ((⨆ x : expansionStructure.Ball r,
      (inclusionTransFormula hrs hst).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) : TruthValue).2.1

/-- In every model of the X ball theory, the identity inclusion has zero
distance from the original point. -/
theorem dist_inclusion_refl_eq_zero_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    (r : ℚ≥0) (x : M.Ball r) :
    dist (M.inclusion (le_refl r) x) x = 0 := by
  have hsentence : (inclusionReflSentence r).value M = zeroTruthValue := by
    calc
      (inclusionReflSentence r).value M =
          (inclusionReflSentence r).value expansionStructure :=
        (hTheory (inclusionReflSentence r)).symm
      _ = zeroTruthValue := inclusionReflSentence_value r
  have hle := realize_le_unarySentence M r (inclusionReflFormula r) x
  change (inclusionReflFormula r).realize M _ ≤
    (inclusionReflSentence r).value M at hle
  rw [hsentence] at hle
  have hzero : (inclusionReflFormula r).realize M
      (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) = zeroTruthValue :=
    le_antisymm hle
      ((inclusionReflFormula r).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).2.1
  have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) hzero
  change dist (M.inclusion (le_refl r) x) x / M.sortBound r = 0 at hcoe
  exact (div_eq_zero_iff.mp hcoe).resolve_right
    (ne_of_gt (M.sortBound_pos r))

/-- In every model of the X ball theory, a composite of radius inclusions has
zero distance from the direct inclusion. -/
theorem dist_inclusion_trans_eq_zero_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    {r s t : ℚ≥0} (hrs : r ≤ s) (hst : s ≤ t) (x : M.Ball r) :
    dist (M.inclusion hst (M.inclusion hrs x))
      (M.inclusion (hrs.trans hst) x) = 0 := by
  have hsentence : (inclusionTransSentence hrs hst).value M =
      zeroTruthValue := by
    calc
      (inclusionTransSentence hrs hst).value M =
          (inclusionTransSentence hrs hst).value expansionStructure :=
        (hTheory (inclusionTransSentence hrs hst)).symm
      _ = zeroTruthValue := inclusionTransSentence_value hrs hst
  have hle := realize_le_unarySentence M r
    (inclusionTransFormula hrs hst) x
  change (inclusionTransFormula hrs hst).realize M _ ≤
    (inclusionTransSentence hrs hst).value M at hle
  rw [hsentence] at hle
  have hzero : (inclusionTransFormula hrs hst).realize M
      (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) = zeroTruthValue :=
    le_antisymm hle
      ((inclusionTransFormula hrs hst).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).2.1
  have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) hzero
  change dist (M.inclusion hst (M.inclusion hrs x))
      (M.inclusion (hrs.trans hst) x) / M.sortBound t = 0 at hcoe
  exact (div_eq_zero_iff.mp hcoe).resolve_right
    (ne_of_gt (M.sortBound_pos t))

/-- The scale converting a normalized distance in radius `r` to the
normalized value of the same ambient distance in a larger radius `s`. -/
def inclusionDistanceScale (r s : ℚ≥0) : ℝ :=
  rationalBallMetricBound r / rationalBallMetricBound s

theorem inclusionDistanceScale_nonneg (r s : ℚ≥0) :
    0 ≤ inclusionDistanceScale r s := by
  exact div_nonneg (rationalBallMetricBound_pos r).le
    (rationalBallMetricBound_pos s).le

theorem inclusionDistanceScale_le_one {r s : ℚ≥0} (h : r ≤ s) :
    inclusionDistanceScale r s ≤ 1 := by
  exact (div_le_one (rationalBallMetricBound_pos s)).2
    (rationalBallMetricBound_mono h)

/-- The discrepancy between distance after inclusion into radius `s` and
the correctly rescaled distance in radius `r`. -/
def inclusionDistanceFormula {r s : ℚ≥0} (h : r ≤ s) :
    BallFormula PredicateSymbol predicateRadius
      (![r, r] : BallContext 2) :=
  .connective
    (scaledAbsoluteDifferenceConnective
      (inclusionDistanceScale r s)
      (inclusionDistanceScale_nonneg r s)
      (inclusionDistanceScale_le_one h))
    ![
      .distance
        (.inclusion h (.variable 0))
        (.inclusion h (.variable 1)),
      .distance (.variable 0) (.variable 1)]

/-- Universal preservation of the normalization-corrected distance by the
inclusion from radius `r` to radius `s`. -/
def inclusionDistanceSentence {r s : ℚ≥0} (h : r ≤ s) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup r (.iSup r (inclusionDistanceFormula h))

/-- Every binary instance is bounded by its twofold universal closure. -/
theorem realize_le_inclusionDistanceSentence
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    {r s : ℚ≥0} (h : r ≤ s) (x y : M.Ball r) :
    (inclusionDistanceFormula h).realize M
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) ≤
      (inclusionDistanceSentence h).value M := by
  apply le_trans
  · exact le_iSup
      (fun z : M.Ball r ↦
        (inclusionDistanceFormula h).realize M
          (Fin.cons z (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) x
  · exact le_iSup
      (fun z : M.Ball r ↦ ⨆ w : M.Ball r,
        (inclusionDistanceFormula h).realize M
          (Fin.cons w (Fin.cons z (fun i : Fin 0 ↦ nomatch i)))) y

/-- In the concrete X expansion, inclusion preserves the actual ambient
distance, hence satisfies the normalization-corrected formula. -/
theorem inclusionDistanceFormula_realize {r s : ℚ≥0} (h : r ≤ s)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r, r] : BallContext 2)) :
    (inclusionDistanceFormula h).realize expansionStructure assignment =
      zeroTruthValue := by
  apply Subtype.ext
  change |dist (assignment 0).1 (assignment 1).1 /
      rationalBallMetricBound s -
    inclusionDistanceScale r s *
      (dist (assignment 0).1 (assignment 1).1 /
        rationalBallMetricBound r)| = 0
  have heq : dist (assignment 0).1 (assignment 1).1 /
        rationalBallMetricBound s =
      inclusionDistanceScale r s *
        (dist (assignment 0).1 (assignment 1).1 /
          rationalBallMetricBound r) := by
    unfold inclusionDistanceScale
    field_simp [ne_of_gt (rationalBallMetricBound_pos r),
      ne_of_gt (rationalBallMetricBound_pos s)]
  rw [heq, sub_self, abs_zero]

/-- Distance preservation is a zero-valued sentence of the distinguished X
theory. -/
@[simp]
theorem inclusionDistanceSentence_value {r s : ℚ≥0} (h : r ≤ s) :
    (inclusionDistanceSentence h).value expansionStructure =
      zeroTruthValue := by
  change (⨆ y : expansionStructure.Ball r,
      ⨆ x : expansionStructure.Ball r,
        (inclusionDistanceFormula h).realize expansionStructure
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) =
    zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun y ↦ iSup_le fun x ↦
      (inclusionDistanceFormula_realize h
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))).le
  · exact ((⨆ y : expansionStructure.Ball r,
      ⨆ x : expansionStructure.Ball r,
        (inclusionDistanceFormula h).realize expansionStructure
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) :
      TruthValue).2.1

/-- Every model of the X ball theory preserves the canonical rescaled
distance under radius inclusions.  This is the target-independent metric law
needed for the directed-union quotient. -/
theorem inclusion_preserves_rescaledDistance_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    {r s : ℚ≥0} (h : r ≤ s) (x y : M.Ball r) :
    rationalBallMetricBound s *
        (dist (M.inclusion h x) (M.inclusion h y) / M.sortBound s) =
      rationalBallMetricBound r * (dist x y / M.sortBound r) := by
  have hsentence : (inclusionDistanceSentence h).value M =
      zeroTruthValue := by
    calc
      (inclusionDistanceSentence h).value M =
          (inclusionDistanceSentence h).value expansionStructure :=
        (hTheory (inclusionDistanceSentence h)).symm
      _ = zeroTruthValue := inclusionDistanceSentence_value h
  have hle := realize_le_inclusionDistanceSentence M h x y
  rw [hsentence] at hle
  have hzero : (inclusionDistanceFormula h).realize M
      (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) =
        zeroTruthValue :=
    le_antisymm hle
      ((inclusionDistanceFormula h).realize M
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))).2.1
  have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) hzero
  change |dist (M.inclusion h x) (M.inclusion h y) / M.sortBound s -
    inclusionDistanceScale r s * (dist x y / M.sortBound r)| = 0 at hcoe
  have hscaled : dist (M.inclusion h x) (M.inclusion h y) / M.sortBound s =
      inclusionDistanceScale r s * (dist x y / M.sortBound r) :=
    sub_eq_zero.mp (abs_eq_zero.mp hcoe)
  rw [hscaled]
  unfold inclusionDistanceScale
  field_simp [ne_of_gt (rationalBallMetricBound_pos s)]

/-! ## Auxiliary-Hilbert predicate coherence -/

/-- The discrepancy between the normalized auxiliary Hilbert predicate after
inclusion into radius `s` and its correctly rescaled value in radius `r`. -/
def inclusionHilbertNormFormula {r s : ℚ≥0} (h : r ≤ s) :
    BallFormula PredicateSymbol predicateRadius
      (![r] : BallContext 1) :=
  .connective
    (scaledAbsoluteDifferenceConnective
      (inclusionDistanceScale r s)
      (inclusionDistanceScale_nonneg r s)
      (inclusionDistanceScale_le_one h))
    ![
      hilbertNormFormula (.inclusion h (.variable 0)),
      hilbertNormFormula (.variable 0)]

/-- Universal coherence of the normalization-corrected auxiliary Hilbert
predicate under inclusion from radius `r` to radius `s`. -/
def inclusionHilbertNormSentence {r s : ℚ≥0} (h : r ≤ s) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup r (inclusionHilbertNormFormula h)

/-- In the concrete X expansion, radius inclusion preserves the underlying
auxiliary Hilbert vector and hence its normalization-corrected norm. -/
theorem inclusionHilbertNormFormula_realize {r s : ℚ≥0} (h : r ≤ s)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r] : BallContext 1)) :
    (inclusionHilbertNormFormula h).realize expansionStructure assignment =
      zeroTruthValue := by
  apply Subtype.ext
  change |‖toHilbert (assignment 0).1‖ / rationalBallMetricBound s -
    inclusionDistanceScale r s *
      (‖toHilbert (assignment 0).1‖ / rationalBallMetricBound r)| = 0
  have heq : ‖toHilbert (assignment 0).1‖ / rationalBallMetricBound s =
      inclusionDistanceScale r s *
        (‖toHilbert (assignment 0).1‖ / rationalBallMetricBound r) := by
    unfold inclusionDistanceScale
    field_simp [ne_of_gt (rationalBallMetricBound_pos r),
      ne_of_gt (rationalBallMetricBound_pos s)]
  rw [heq, sub_self, abs_zero]

/-- Auxiliary-Hilbert inclusion coherence is a zero-valued sentence of the
distinguished X theory. -/
@[simp]
theorem inclusionHilbertNormSentence_value {r s : ℚ≥0} (h : r ≤ s) :
    (inclusionHilbertNormSentence h).value expansionStructure =
      zeroTruthValue := by
  change (⨆ x : expansionStructure.Ball r,
      (inclusionHilbertNormFormula h).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) = zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun x ↦
      (inclusionHilbertNormFormula_realize h
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).le
  · exact ((⨆ x : expansionStructure.Ball r,
      (inclusionHilbertNormFormula h).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) : TruthValue).2.1

/-- Every model of the complete X ball theory preserves the unnormalized
auxiliary Hilbert value under radius inclusion. -/
theorem inclusion_preserves_rescaledHilbertNorm_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    {r s : ℚ≥0} (h : r ≤ s) (x : M.Ball r) :
    rationalBallMetricBound s *
        (M.predicate (.hilbert s) (M.inclusion h x) : ℝ) =
      rationalBallMetricBound r *
        (M.predicate (.hilbert r) x : ℝ) := by
  have hsentence : (inclusionHilbertNormSentence h).value M =
      zeroTruthValue := by
    calc
      (inclusionHilbertNormSentence h).value M =
          (inclusionHilbertNormSentence h).value expansionStructure :=
        (hTheory (inclusionHilbertNormSentence h)).symm
      _ = zeroTruthValue := inclusionHilbertNormSentence_value h
  have hle := realize_le_unarySentence M r
    (inclusionHilbertNormFormula h) x
  change (inclusionHilbertNormFormula h).realize M _ ≤
    (inclusionHilbertNormSentence h).value M at hle
  rw [hsentence] at hle
  have hzero : (inclusionHilbertNormFormula h).realize M
      (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) = zeroTruthValue :=
    le_antisymm hle
      ((inclusionHilbertNormFormula h).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).2.1
  have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) hzero
  change |(M.predicate (.hilbert s) (M.inclusion h x) : ℝ) -
    inclusionDistanceScale r s *
      (M.predicate (.hilbert r) x : ℝ)| = 0 at hcoe
  have hscaled :
      (M.predicate (.hilbert s) (M.inclusion h x) : ℝ) =
        inclusionDistanceScale r s *
          (M.predicate (.hilbert r) x : ℝ) :=
    sub_eq_zero.mp (abs_eq_zero.mp hcoe)
  rw [hscaled]
  unfold inclusionDistanceScale
  field_simp [ne_of_gt (rationalBallMetricBound_pos s)]

/-- Failure of the sharp reverse-triangle estimate for the normalized
auxiliary Hilbert predicate on one radius sort. -/
def hilbertNormDistanceFormula (r : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius
      (![r, r] : BallContext 2) :=
  .connective (scaledOrderViolationConnective 1 (by norm_num)) ![
    .connective absoluteDifferenceConnective ![
      hilbertNormFormula (.variable 0),
      hilbertNormFormula (.variable 1)],
    .distance (.variable 0) (.variable 1)]

/-- Universal sharp Lipschitz sentence for the radius-`r` auxiliary Hilbert
predicate. -/
def hilbertNormDistanceSentence (r : ℚ≥0) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup r (.iSup r (hilbertNormDistanceFormula r))

/-- Every binary instance is bounded by its twofold universal closure. -/
theorem realize_le_hilbertNormDistanceSentence
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (r : ℚ≥0) (x y : M.Ball r) :
    (hilbertNormDistanceFormula r).realize M
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) ≤
      (hilbertNormDistanceSentence r).value M := by
  apply le_trans
  · exact le_iSup
      (fun z : M.Ball r ↦
        (hilbertNormDistanceFormula r).realize M
          (Fin.cons z (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) x
  · exact le_iSup
      (fun z : M.Ball r ↦ ⨆ w : M.Ball r,
        (hilbertNormDistanceFormula r).realize M
          (Fin.cons w (Fin.cons z (fun i : Fin 0 ↦ nomatch i)))) y

/-- The normalized auxiliary Hilbert predicate is sharply Lipschitz in the
concrete X expansion. -/
theorem hilbertNormDistanceFormula_realize (r : ℚ≥0)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r, r] : BallContext 2)) :
    (hilbertNormDistanceFormula r).realize expansionStructure assignment =
      zeroTruthValue := by
  apply (scaledOrderViolationConnective_eq_zero_iff 1 (by norm_num) _).2
  change |‖toHilbert (assignment 0).1‖ / rationalBallMetricBound r -
      ‖toHilbert (assignment 1).1‖ / rationalBallMetricBound r| ≤
    1 * (dist (assignment 0).1 (assignment 1).1 /
      rationalBallMetricBound r)
  rw [one_mul, ← sub_div]
  have hnorm :
      |‖toHilbert (assignment 0).1‖ - ‖toHilbert (assignment 1).1‖| ≤
        dist (assignment 0).1 (assignment 1).1 := by
    calc
      |‖toHilbert (assignment 0).1‖ - ‖toHilbert (assignment 1).1‖| ≤
          ‖toHilbert (assignment 0).1 - toHilbert (assignment 1).1‖ :=
        abs_norm_sub_norm_le _ _
      _ = ‖toHilbert ((assignment 0).1 - (assignment 1).1)‖ := by
        change ‖linearEquivHilbertSum (assignment 0).1 -
            linearEquivHilbertSum (assignment 1).1‖ =
          ‖linearEquivHilbertSum ((assignment 0).1 - (assignment 1).1)‖
        rw [map_sub]
      _ ≤ ‖(assignment 0).1 - (assignment 1).1‖ :=
        norm_toHilbert_le _
      _ = dist (assignment 0).1 (assignment 1).1 := by
        rw [dist_eq_norm]
  rw [abs_div, abs_of_pos (rationalBallMetricBound_pos r)]
  exact div_le_div_of_nonneg_right hnorm
    (rationalBallMetricBound_pos r).le

/-- The sharp Hilbert-predicate Lipschitz law is a zero-valued sentence of
the distinguished X theory. -/
@[simp]
theorem hilbertNormDistanceSentence_value (r : ℚ≥0) :
    (hilbertNormDistanceSentence r).value expansionStructure =
      zeroTruthValue := by
  change (⨆ y : expansionStructure.Ball r,
      ⨆ x : expansionStructure.Ball r,
        (hilbertNormDistanceFormula r).realize expansionStructure
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) =
    zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun y ↦ iSup_le fun x ↦
      (hilbertNormDistanceFormula_realize r
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))).le
  · exact ((⨆ y : expansionStructure.Ball r,
      ⨆ x : expansionStructure.Ball r,
        (hilbertNormDistanceFormula r).realize expansionStructure
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) :
      TruthValue).2.1

/-- Every model of the complete X ball theory satisfies the sharp
normalization-corrected Lipschitz estimate for its auxiliary Hilbert
predicate. -/
theorem hilbertNorm_rescaledDistance_le_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    (r : ℚ≥0) (x y : M.Ball r) :
    |rationalBallMetricBound r *
          (M.predicate (.hilbert r) x : ℝ) -
        rationalBallMetricBound r *
          (M.predicate (.hilbert r) y : ℝ)| ≤
      rationalBallMetricBound r * (dist x y / M.sortBound r) := by
  have hsentence : (hilbertNormDistanceSentence r).value M =
      zeroTruthValue := by
    calc
      (hilbertNormDistanceSentence r).value M =
          (hilbertNormDistanceSentence r).value expansionStructure :=
        (hTheory (hilbertNormDistanceSentence r)).symm
      _ = zeroTruthValue := hilbertNormDistanceSentence_value r
  have hle := realize_le_hilbertNormDistanceSentence M r x y
  rw [hsentence] at hle
  have hzero : (hilbertNormDistanceFormula r).realize M
      (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) =
        zeroTruthValue :=
    le_antisymm hle
      ((hilbertNormDistanceFormula r).realize M
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))).2.1
  have hnormalized :=
    (scaledOrderViolationConnective_eq_zero_iff 1 (by norm_num) _).1 hzero
  change |(M.predicate (.hilbert r) x : ℝ) -
      (M.predicate (.hilbert r) y : ℝ)| ≤
    1 * (dist x y / M.sortBound r) at hnormalized
  rw [one_mul] at hnormalized
  calc
    |rationalBallMetricBound r *
          (M.predicate (.hilbert r) x : ℝ) -
        rationalBallMetricBound r *
          (M.predicate (.hilbert r) y : ℝ)| =
        rationalBallMetricBound r *
          |(M.predicate (.hilbert r) x : ℝ) -
            (M.predicate (.hilbert r) y : ℝ)| := by
      rw [← mul_sub, abs_mul,
        abs_of_pos (rationalBallMetricBound_pos r)]
    _ ≤ rationalBallMetricBound r * (dist x y / M.sortBound r) :=
      mul_le_mul_of_nonneg_left hnormalized
        (rationalBallMetricBound_pos r).le

/-! ## Rational homogeneity of the auxiliary-Hilbert predicate -/

/-- A positive common denominator used to compare the independently
normalized input and output Hilbert predicates of a rational scalar term. -/
def smulHilbertNormDenominator (q : ℚ) (r : ℚ≥0) : ℝ :=
  rationalBallMetricBound (q.nnabs * r) +
    (q.nnabs : ℝ) * rationalBallMetricBound r

theorem smulHilbertNormDenominator_pos (q : ℚ) (r : ℚ≥0) :
    0 < smulHilbertNormDenominator q r := by
  unfold smulHilbertNormDenominator
  exact add_pos_of_pos_of_nonneg
    (rationalBallMetricBound_pos (q.nnabs * r))
    (mul_nonneg (NNRat.cast_nonneg q.nnabs)
      (rationalBallMetricBound_pos r).le)

/-- Coefficient of the output predicate after division by the common
homogeneity denominator. -/
def smulHilbertNormOutputScale (q : ℚ) (r : ℚ≥0) : ℝ :=
  rationalBallMetricBound (q.nnabs * r) /
    smulHilbertNormDenominator q r

/-- Coefficient of the input predicate after division by the common
homogeneity denominator. -/
def smulHilbertNormInputScale (q : ℚ) (r : ℚ≥0) : ℝ :=
  ((q.nnabs : ℝ) * rationalBallMetricBound r) /
    smulHilbertNormDenominator q r

theorem smulHilbertNormOutputScale_nonneg (q : ℚ) (r : ℚ≥0) :
    0 ≤ smulHilbertNormOutputScale q r := by
  exact div_nonneg (rationalBallMetricBound_pos (q.nnabs * r)).le
    (smulHilbertNormDenominator_pos q r).le

theorem smulHilbertNormOutputScale_le_one (q : ℚ) (r : ℚ≥0) :
    smulHilbertNormOutputScale q r ≤ 1 := by
  apply (div_le_one (smulHilbertNormDenominator_pos q r)).2
  unfold smulHilbertNormDenominator
  exact le_add_of_nonneg_right
    (mul_nonneg (NNRat.cast_nonneg q.nnabs)
      (rationalBallMetricBound_pos r).le)

theorem smulHilbertNormInputScale_nonneg (q : ℚ) (r : ℚ≥0) :
    0 ≤ smulHilbertNormInputScale q r := by
  exact div_nonneg
    (mul_nonneg (NNRat.cast_nonneg q.nnabs)
      (rationalBallMetricBound_pos r).le)
    (smulHilbertNormDenominator_pos q r).le

theorem smulHilbertNormInputScale_le_one (q : ℚ) (r : ℚ≥0) :
    smulHilbertNormInputScale q r ≤ 1 := by
  apply (div_le_one (smulHilbertNormDenominator_pos q r)).2
  unfold smulHilbertNormDenominator
  exact le_add_of_nonneg_left
    (rationalBallMetricBound_pos (q.nnabs * r)).le

/-- The normalized discrepancy expressing exact rational homogeneity of the
auxiliary-Hilbert predicate. -/
def smulHilbertNormFormula (q : ℚ) (r : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius
      (![r] : BallContext 1) :=
  .connective
    (doublyScaledAbsoluteDifferenceConnective
      (smulHilbertNormOutputScale q r)
      (smulHilbertNormInputScale q r)
      (smulHilbertNormOutputScale_nonneg q r)
      (smulHilbertNormOutputScale_le_one q r)
      (smulHilbertNormInputScale_nonneg q r)
      (smulHilbertNormInputScale_le_one q r))
    ![
      hilbertNormFormula (.smul q (.variable 0)),
      hilbertNormFormula (.variable 0)]

/-- Universal rational homogeneity of the auxiliary-Hilbert predicate on
the radius-`r` sort. -/
def smulHilbertNormSentence (q : ℚ) (r : ℚ≥0) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup r (smulHilbertNormFormula q r)

/-- The rational homogeneity formula vanishes pointwise in the concrete X
expansion. -/
theorem smulHilbertNormFormula_realize (q : ℚ) (r : ℚ≥0)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r] : BallContext 1)) :
    (smulHilbertNormFormula q r).realize expansionStructure assignment =
      zeroTruthValue := by
  apply (doublyScaledAbsoluteDifferenceConnective_eq_zero_iff
    (smulHilbertNormOutputScale q r)
    (smulHilbertNormInputScale q r)
    (smulHilbertNormOutputScale_nonneg q r)
    (smulHilbertNormOutputScale_le_one q r)
    (smulHilbertNormInputScale_nonneg q r)
    (smulHilbertNormInputScale_le_one q r) _).2
  change smulHilbertNormOutputScale q r *
      (‖toHilbert ((q : ℝ) • (assignment 0).1)‖ /
        rationalBallMetricBound (q.nnabs * r)) =
    smulHilbertNormInputScale q r *
      (‖toHilbert (assignment 0).1‖ / rationalBallMetricBound r)
  have hmap :
      toHilbert ((q : ℝ) • (assignment 0).1) =
        (q : ℝ) • toHilbert (assignment 0).1 := by
    change linearEquivHilbertSum ((q : ℝ) • (assignment 0).1) =
      (q : ℝ) • linearEquivHilbertSum (assignment 0).1
    rw [map_smul]
  rw [hmap, norm_smul, Real.norm_eq_abs]
  have hq : |(q : ℝ)| = (q.nnabs : ℝ) := by norm_cast
  rw [hq]
  unfold smulHilbertNormOutputScale smulHilbertNormInputScale
  field_simp [ne_of_gt (smulHilbertNormDenominator_pos q r),
    ne_of_gt (rationalBallMetricBound_pos r),
    ne_of_gt (rationalBallMetricBound_pos (q.nnabs * r))]

/-- Rational Hilbert homogeneity is a zero-valued sentence of the
distinguished X theory. -/
@[simp] theorem smulHilbertNormSentence_value (q : ℚ) (r : ℚ≥0) :
    (smulHilbertNormSentence q r).value expansionStructure =
      zeroTruthValue := by
  change (⨆ x : expansionStructure.Ball r,
      (smulHilbertNormFormula q r).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) = zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun x ↦
      (smulHilbertNormFormula_realize q r
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).le
  · exact ((⨆ x : expansionStructure.Ball r,
      (smulHilbertNormFormula q r).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) : TruthValue).2.1

/-- Every model of the complete X ball theory satisfies exact rational
homogeneity of the unnormalized auxiliary-Hilbert value. -/
theorem smul_preserves_rescaledHilbertNorm_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    (q : ℚ) (r : ℚ≥0) (x : M.Ball r) :
    rationalBallMetricBound (q.nnabs * r) *
        (M.predicate (.hilbert (q.nnabs * r)) (M.smul q r x) : ℝ) =
      (q.nnabs : ℝ) * rationalBallMetricBound r *
        (M.predicate (.hilbert r) x : ℝ) := by
  have hsentence : (smulHilbertNormSentence q r).value M =
      zeroTruthValue := by
    calc
      (smulHilbertNormSentence q r).value M =
          (smulHilbertNormSentence q r).value expansionStructure :=
        (hTheory (smulHilbertNormSentence q r)).symm
      _ = zeroTruthValue := smulHilbertNormSentence_value q r
  have hle := realize_le_unarySentence M r
    (smulHilbertNormFormula q r) x
  change (smulHilbertNormFormula q r).realize M _ ≤
    (smulHilbertNormSentence q r).value M at hle
  rw [hsentence] at hle
  have hzero : (smulHilbertNormFormula q r).realize M
      (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) = zeroTruthValue :=
    le_antisymm hle
      ((smulHilbertNormFormula q r).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).2.1
  have hscaled :=
    (doublyScaledAbsoluteDifferenceConnective_eq_zero_iff
      (smulHilbertNormOutputScale q r)
      (smulHilbertNormInputScale q r)
      (smulHilbertNormOutputScale_nonneg q r)
      (smulHilbertNormOutputScale_le_one q r)
      (smulHilbertNormInputScale_nonneg q r)
      (smulHilbertNormInputScale_le_one q r) _).1 hzero
  change smulHilbertNormOutputScale q r *
      (M.predicate (.hilbert (q.nnabs * r)) (M.smul q r x) : ℝ) =
    smulHilbertNormInputScale q r *
      (M.predicate (.hilbert r) x : ℝ) at hscaled
  unfold smulHilbertNormOutputScale smulHilbertNormInputScale at hscaled
  field_simp [ne_of_gt (smulHilbertNormDenominator_pos q r)] at hscaled
  exact hscaled

/-- The distance-zero sentence asserting that the radius-`r` zero becomes the
radius-`s` zero under inclusion. -/
def inclusionZeroSentence {r s : ℚ≥0} (h : r ≤ s) :
    BallSentence PredicateSymbol predicateRadius :=
  .distance
    (.inclusion h (.zero r))
    (.zero s)

/-- Failure of inclusion to commute with negation on the radius-`r` sort. -/
def inclusionNegFormula {r s : ℚ≥0} (h : r ≤ s) :
    BallFormula PredicateSymbol predicateRadius
      (![r] : BallContext 1) :=
  .distance
    (.inclusion h (.neg (.variable 0)))
    (.neg (.inclusion h (.variable 0)))

/-- Universal compatibility of inclusion with negation. -/
def inclusionNegSentence {r s : ℚ≥0} (h : r ≤ s) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup r (inclusionNegFormula h)

/-- Concrete radius inclusions preserve zero. -/
@[simp]
theorem inclusionZeroSentence_value {r s : ℚ≥0} (h : r ≤ s) :
    (inclusionZeroSentence h).value expansionStructure = zeroTruthValue := by
  apply Subtype.ext
  change dist
      (rationalBallInclusion (E := XSpace) h
        (rationalBallZero (E := XSpace) r))
      (rationalBallZero (E := XSpace) s) /
        rationalBallMetricBound s = 0
  change dist (0 : XSpace) 0 / rationalBallMetricBound s = 0
  simp

/-- Concrete radius inclusions commute with negation pointwise. -/
theorem inclusionNegFormula_realize {r s : ℚ≥0} (h : r ≤ s)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r] : BallContext 1)) :
    (inclusionNegFormula h).realize expansionStructure assignment =
      zeroTruthValue := by
  apply Subtype.ext
  change dist
      (rationalBallInclusion (E := XSpace) h
        (rationalBallNeg (E := XSpace) r (assignment 0)))
      (rationalBallNeg (E := XSpace) s
        (rationalBallInclusion (E := XSpace) h (assignment 0))) /
        rationalBallMetricBound s = 0
  change dist (-(assignment 0).1) (-(assignment 0).1) /
    rationalBallMetricBound s = 0
  simp

/-- Inclusion--negation compatibility is a zero-valued sentence of the
distinguished X theory. -/
@[simp]
theorem inclusionNegSentence_value {r s : ℚ≥0} (h : r ≤ s) :
    (inclusionNegSentence h).value expansionStructure = zeroTruthValue := by
  change (⨆ x : expansionStructure.Ball r,
      (inclusionNegFormula h).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) = zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun x ↦
      (inclusionNegFormula_realize h
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).le
  · exact ((⨆ x : expansionStructure.Ball r,
      (inclusionNegFormula h).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) : TruthValue).2.1

/-- Every model of the X ball theory preserves zero across radius
inclusions, up to the ambient pseudometric. -/
theorem dist_inclusion_zero_eq_zero_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    {r s : ℚ≥0} (h : r ≤ s) :
    dist (M.inclusion h (M.zero r)) (M.zero s) = 0 := by
  have hvalue : (inclusionZeroSentence h).value M = zeroTruthValue := by
    calc
      (inclusionZeroSentence h).value M =
          (inclusionZeroSentence h).value expansionStructure :=
        (hTheory (inclusionZeroSentence h)).symm
      _ = zeroTruthValue := inclusionZeroSentence_value h
  have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) hvalue
  change dist (M.inclusion h (M.zero r)) (M.zero s) /
      M.sortBound s = 0 at hcoe
  exact (div_eq_zero_iff.mp hcoe).resolve_right
    (ne_of_gt (M.sortBound_pos s))

/-- Every model of the X ball theory makes radius inclusion commute with
negation up to zero pseudodistance. -/
theorem dist_inclusion_neg_eq_zero_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    {r s : ℚ≥0} (h : r ≤ s) (x : M.Ball r) :
    dist (M.inclusion h (M.neg r x))
      (M.neg s (M.inclusion h x)) = 0 := by
  have hsentence : (inclusionNegSentence h).value M = zeroTruthValue := by
    calc
      (inclusionNegSentence h).value M =
          (inclusionNegSentence h).value expansionStructure :=
        (hTheory (inclusionNegSentence h)).symm
      _ = zeroTruthValue := inclusionNegSentence_value h
  have hle := realize_le_unarySentence M r (inclusionNegFormula h) x
  change (inclusionNegFormula h).realize M _ ≤
    (inclusionNegSentence h).value M at hle
  rw [hsentence] at hle
  have hzero : (inclusionNegFormula h).realize M
      (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) = zeroTruthValue :=
    le_antisymm hle
      ((inclusionNegFormula h).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).2.1
  have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) hzero
  change dist (M.inclusion h (M.neg r x))
      (M.neg s (M.inclusion h x)) / M.sortBound s = 0 at hcoe
  exact (div_eq_zero_iff.mp hcoe).resolve_right
    (ne_of_gt (M.sortBound_pos s))

/-- Failure of the addition square for radius enlargements `r → r'` and
`s → s'`. -/
def inclusionAddFormula {r r' s s' : ℚ≥0}
    (hr : r ≤ r') (hs : s ≤ s') :
    BallFormula PredicateSymbol predicateRadius
      (![r, s] : BallContext 2) :=
  .distance
    (.inclusion (add_le_add hr hs)
      (.add (.variable 0) (.variable 1)))
    (.add
      (.inclusion hr (.variable 0))
      (.inclusion hs (.variable 1)))

/-- Universal compatibility of inclusion with binary addition. -/
def inclusionAddSentence {r r' s s' : ℚ≥0}
    (hr : r ≤ r') (hs : s ≤ s') :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup s (.iSup r (inclusionAddFormula hr hs))

/-- Every mixed-radius binary instance is bounded by its universal closure. -/
theorem realize_le_inclusionAddSentence
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    {r r' s s' : ℚ≥0} (hr : r ≤ r') (hs : s ≤ s')
    (x : M.Ball r) (y : M.Ball s) :
    (inclusionAddFormula hr hs).realize M
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) ≤
      (inclusionAddSentence hr hs).value M := by
  apply le_trans
  · exact le_iSup
      (fun z : M.Ball r ↦
        (inclusionAddFormula hr hs).realize M
          (Fin.cons z (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) x
  · exact le_iSup
      (fun z : M.Ball s ↦ ⨆ w : M.Ball r,
        (inclusionAddFormula hr hs).realize M
          (Fin.cons w (Fin.cons z (fun i : Fin 0 ↦ nomatch i)))) y

/-- Concrete ball inclusions commute with binary addition pointwise. -/
theorem inclusionAddFormula_realize {r r' s s' : ℚ≥0}
    (hr : r ≤ r') (hs : s ≤ s')
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r, s] : BallContext 2)) :
    (inclusionAddFormula (r := r) (r' := r') (s := s) (s' := s') hr hs).realize
        expansionStructure assignment =
      zeroTruthValue := by
  apply Subtype.ext
  change dist
      (rationalBallInclusion (E := XSpace) (add_le_add hr hs)
        (rationalBallAdd (E := XSpace) r s
          (assignment 0, assignment 1)))
      (rationalBallAdd (E := XSpace) r' s'
        (rationalBallInclusion (E := XSpace) hr (assignment 0),
          rationalBallInclusion (E := XSpace) hs (assignment 1))) /
        rationalBallMetricBound (r' + s') = 0
  rw [rationalBallInclusion_add (E := XSpace) hr hs
    (assignment 0) (assignment 1)]
  simp

/-- Addition coherence is a zero-valued sentence of the distinguished X
theory. -/
@[simp]
theorem inclusionAddSentence_value {r r' s s' : ℚ≥0}
    (hr : r ≤ r') (hs : s ≤ s') :
    (inclusionAddSentence hr hs).value expansionStructure =
      zeroTruthValue := by
  change (⨆ y : expansionStructure.Ball s,
      ⨆ x : expansionStructure.Ball r,
        (inclusionAddFormula hr hs).realize expansionStructure
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) =
    zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun y ↦ iSup_le fun x ↦
      (inclusionAddFormula_realize hr hs
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))).le
  · exact ((⨆ y : expansionStructure.Ball s,
      ⨆ x : expansionStructure.Ball r,
        (inclusionAddFormula hr hs).realize expansionStructure
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) :
      TruthValue).2.1

/-- Every model of the X ball theory makes radius inclusion commute with
binary addition up to zero pseudodistance. -/
theorem dist_inclusion_add_eq_zero_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    {r r' s s' : ℚ≥0} (hr : r ≤ r') (hs : s ≤ s')
    (x : M.Ball r) (y : M.Ball s) :
    dist
      (M.inclusion (add_le_add hr hs) (M.add r s (x, y)))
      (M.add r' s' (M.inclusion hr x, M.inclusion hs y)) = 0 := by
  have hsentence : (inclusionAddSentence hr hs).value M =
      zeroTruthValue := by
    calc
      (inclusionAddSentence hr hs).value M =
          (inclusionAddSentence hr hs).value expansionStructure :=
        (hTheory (inclusionAddSentence hr hs)).symm
      _ = zeroTruthValue := inclusionAddSentence_value hr hs
  have hle := realize_le_inclusionAddSentence M hr hs x y
  rw [hsentence] at hle
  have hzero : (inclusionAddFormula hr hs).realize M
      (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) =
        zeroTruthValue :=
    le_antisymm hle
      ((inclusionAddFormula hr hs).realize M
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))).2.1
  have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) hzero
  change dist
      (M.inclusion (add_le_add hr hs) (M.add r s (x, y)))
      (M.add r' s' (M.inclusion hr x, M.inclusion hs y)) /
        M.sortBound (r' + s') = 0 at hcoe
  exact (div_eq_zero_iff.mp hcoe).resolve_right
    (ne_of_gt (M.sortBound_pos (r' + s')))

/-- Monotonicity of the exact output radius for rational scalar
multiplication. -/
theorem nnabs_mul_mono {r s : ℚ≥0} (h : r ≤ s) (q : ℚ) :
    q.nnabs * r ≤ q.nnabs * s :=
  mul_le_mul_right h q.nnabs

/-- Failure of the scalar-multiplication square for a radius enlargement. -/
def inclusionSmulFormula {r s : ℚ≥0} (h : r ≤ s) (q : ℚ) :
    BallFormula PredicateSymbol predicateRadius
      (![r] : BallContext 1) :=
  .distance
    (.inclusion (nnabs_mul_mono h q)
      (.smul q (.variable 0)))
    (.smul q (.inclusion h (.variable 0)))

/-- Universal compatibility of inclusion with rational scalar
multiplication. -/
def inclusionSmulSentence {r s : ℚ≥0} (h : r ≤ s) (q : ℚ) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup r (inclusionSmulFormula h q)

/-- Concrete ball inclusions commute with rational scalar multiplication. -/
theorem inclusionSmulFormula_realize {r s : ℚ≥0} (h : r ≤ s) (q : ℚ)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r] : BallContext 1)) :
    (inclusionSmulFormula h q).realize expansionStructure assignment =
      zeroTruthValue := by
  apply Subtype.ext
  change dist
      (rationalBallInclusion (E := XSpace) (nnabs_mul_mono h q)
        (rationalBallSmul (E := XSpace) q r (assignment 0)))
      (rationalBallSmul (E := XSpace) q s
        (rationalBallInclusion (E := XSpace) h (assignment 0))) /
        rationalBallMetricBound (q.nnabs * s) = 0
  rw [rationalBallInclusion_smul (E := XSpace) h q (assignment 0)]
  simp

/-- Scalar-multiplication coherence is a zero-valued sentence of the
distinguished X theory. -/
@[simp]
theorem inclusionSmulSentence_value {r s : ℚ≥0} (h : r ≤ s) (q : ℚ) :
    (inclusionSmulSentence h q).value expansionStructure =
      zeroTruthValue := by
  change (⨆ x : expansionStructure.Ball r,
      (inclusionSmulFormula h q).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) = zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun x ↦
      (inclusionSmulFormula_realize h q
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).le
  · exact ((⨆ x : expansionStructure.Ball r,
      (inclusionSmulFormula h q).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) : TruthValue).2.1

/-- Every model of the X ball theory makes radius inclusion commute with
rational scalar multiplication up to zero pseudodistance. -/
theorem dist_inclusion_smul_eq_zero_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    {r s : ℚ≥0} (h : r ≤ s) (q : ℚ) (x : M.Ball r) :
    dist
      (M.inclusion (nnabs_mul_mono h q) (M.smul q r x))
      (M.smul q s (M.inclusion h x)) = 0 := by
  have hsentence : (inclusionSmulSentence h q).value M =
      zeroTruthValue := by
    calc
      (inclusionSmulSentence h q).value M =
          (inclusionSmulSentence h q).value expansionStructure :=
        (hTheory (inclusionSmulSentence h q)).symm
      _ = zeroTruthValue := inclusionSmulSentence_value h q
  have hle := realize_le_unarySentence M r (inclusionSmulFormula h q) x
  change (inclusionSmulFormula h q).realize M _ ≤
    (inclusionSmulSentence h q).value M at hle
  rw [hsentence] at hle
  have hzero : (inclusionSmulFormula h q).realize M
      (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) = zeroTruthValue :=
    le_antisymm hle
      ((inclusionSmulFormula h q).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).2.1
  have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) hzero
  change dist
      (M.inclusion (nnabs_mul_mono h q) (M.smul q r x))
      (M.smul q s (M.inclusion h x)) /
        M.sortBound (q.nnabs * s) = 0 at hcoe
  exact (div_eq_zero_iff.mp hcoe).resolve_right
    (ne_of_gt (M.sortBound_pos (q.nnabs * s)))

/-! ## First transferred algebraic identity -/

/-- Failure of involutive negation in one radius sort. -/
def negNegFormula (r : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius
      (![r] : BallContext 1) :=
  .distance (.neg (.neg (.variable 0))) (.variable 0)

/-- Universal involutive-negation sentence at radius `r`. -/
def negNegSentence (r : ℚ≥0) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup r (negNegFormula r)

/-- Double negation has zero discrepancy in the distinguished X expansion. -/
theorem negNegFormula_realize (r : ℚ≥0)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r] : BallContext 1)) :
    (negNegFormula r).realize expansionStructure assignment =
      zeroTruthValue := by
  apply Subtype.ext
  change dist (-(-((assignment 0).1))) (assignment 0).1 /
      rationalBallMetricBound r = 0
  simp

/-- Involutive negation is a zero-valued sentence of the distinguished X
complete theory. -/
@[simp] theorem negNegSentence_value (r : ℚ≥0) :
    (negNegSentence r).value expansionStructure = zeroTruthValue := by
  change (⨆ x : expansionStructure.Ball r,
      (negNegFormula r).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) = zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun x ↦
      (negNegFormula_realize r
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).le
  · exact ((⨆ x : expansionStructure.Ball r,
      (negNegFormula r).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) : TruthValue).2.1

/-- Every model of the complete typed X theory has involutive negation up to
zero pseudodistance. -/
theorem dist_neg_neg_eq_zero_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    (r : ℚ≥0) (x : M.Ball r) :
    dist (M.neg r (M.neg r x)) x = 0 := by
  have hsentence : (negNegSentence r).value M = zeroTruthValue := by
    calc
      (negNegSentence r).value M =
          (negNegSentence r).value expansionStructure :=
        (hTheory (negNegSentence r)).symm
      _ = zeroTruthValue := negNegSentence_value r
  have hle := realize_le_unarySentence M r (negNegFormula r) x
  change (negNegFormula r).realize M _ ≤
    (negNegSentence r).value M at hle
  rw [hsentence] at hle
  have hzero : (negNegFormula r).realize M
      (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) = zeroTruthValue :=
    le_antisymm hle
      ((negNegFormula r).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).2.1
  have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) hzero
  change dist (M.neg r (M.neg r x)) x / M.sortBound r = 0 at hcoe
  exact (div_eq_zero_iff.mp hcoe).resolve_right
    (ne_of_gt (M.sortBound_pos r))

/-- Failure of the right zero law, compared in the radius `r+r` sort. -/
def addZeroFormula (r : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius
      (![r] : BallContext 1) :=
  .distance
    (.add (.variable 0) (.zero r))
    (.inclusion (le_add_of_nonneg_right (zero_le r)) (.variable 0))

/-- Failure of the left zero law, compared in the radius `r+r` sort. -/
def zeroAddFormula (r : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius
      (![r] : BallContext 1) :=
  .distance
    (.add (.zero r) (.variable 0))
    (.inclusion (le_add_of_nonneg_left (zero_le r)) (.variable 0))

def addZeroSentence (r : ℚ≥0) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup r (addZeroFormula r)

def zeroAddSentence (r : ℚ≥0) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup r (zeroAddFormula r)

theorem addZeroFormula_realize (r : ℚ≥0)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r] : BallContext 1)) :
    (addZeroFormula r).realize expansionStructure assignment =
      zeroTruthValue := by
  apply Subtype.ext
  change dist ((assignment 0).1 + 0) (assignment 0).1 /
      rationalBallMetricBound (r + r) = 0
  simp

theorem zeroAddFormula_realize (r : ℚ≥0)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r] : BallContext 1)) :
    (zeroAddFormula r).realize expansionStructure assignment =
      zeroTruthValue := by
  apply Subtype.ext
  change dist (0 + (assignment 0).1) (assignment 0).1 /
      rationalBallMetricBound (r + r) = 0
  simp

@[simp] theorem addZeroSentence_value (r : ℚ≥0) :
    (addZeroSentence r).value expansionStructure = zeroTruthValue := by
  change (⨆ x : expansionStructure.Ball r,
      (addZeroFormula r).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) = zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun x ↦
      (addZeroFormula_realize r
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).le
  · exact ((⨆ x : expansionStructure.Ball r,
      (addZeroFormula r).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) : TruthValue).2.1

@[simp] theorem zeroAddSentence_value (r : ℚ≥0) :
    (zeroAddSentence r).value expansionStructure = zeroTruthValue := by
  change (⨆ x : expansionStructure.Ball r,
      (zeroAddFormula r).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) = zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun x ↦
      (zeroAddFormula_realize r
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).le
  · exact ((⨆ x : expansionStructure.Ball r,
      (zeroAddFormula r).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) : TruthValue).2.1

theorem dist_add_zero_eq_zero_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    (r : ℚ≥0) (x : M.Ball r) :
    dist (M.add r r (x, M.zero r))
      (M.inclusion (le_add_of_nonneg_right (zero_le r)) x) = 0 := by
  have hsentence : (addZeroSentence r).value M = zeroTruthValue := by
    calc
      (addZeroSentence r).value M =
          (addZeroSentence r).value expansionStructure :=
        (hTheory (addZeroSentence r)).symm
      _ = zeroTruthValue := addZeroSentence_value r
  have hle := realize_le_unarySentence M r (addZeroFormula r) x
  change (addZeroFormula r).realize M _ ≤
    (addZeroSentence r).value M at hle
  rw [hsentence] at hle
  have hzero : (addZeroFormula r).realize M
      (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) = zeroTruthValue :=
    le_antisymm hle
      ((addZeroFormula r).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).2.1
  have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) hzero
  change dist (M.add r r (x, M.zero r))
      (M.inclusion (le_add_of_nonneg_right (zero_le r)) x) /
        M.sortBound (r + r) = 0 at hcoe
  exact (div_eq_zero_iff.mp hcoe).resolve_right
    (ne_of_gt (M.sortBound_pos (r + r)))

theorem dist_zero_add_eq_zero_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    (r : ℚ≥0) (x : M.Ball r) :
    dist (M.add r r (M.zero r, x))
      (M.inclusion (le_add_of_nonneg_left (zero_le r)) x) = 0 := by
  have hsentence : (zeroAddSentence r).value M = zeroTruthValue := by
    calc
      (zeroAddSentence r).value M =
          (zeroAddSentence r).value expansionStructure :=
        (hTheory (zeroAddSentence r)).symm
      _ = zeroTruthValue := zeroAddSentence_value r
  have hle := realize_le_unarySentence M r (zeroAddFormula r) x
  change (zeroAddFormula r).realize M _ ≤
    (zeroAddSentence r).value M at hle
  rw [hsentence] at hle
  have hzero : (zeroAddFormula r).realize M
      (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) = zeroTruthValue :=
    le_antisymm hle
      ((zeroAddFormula r).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).2.1
  have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) hzero
  change dist (M.add r r (M.zero r, x))
      (M.inclusion (le_add_of_nonneg_left (zero_le r)) x) /
        M.sortBound (r + r) = 0 at hcoe
  exact (div_eq_zero_iff.mp hcoe).resolve_right
    (ne_of_gt (M.sortBound_pos (r + r)))

/-- Failure of right additive cancellation in the radius `r+r` sort. -/
def addNegFormula (r : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius
      (![r] : BallContext 1) :=
  .distance
    (.add (.variable 0) (.neg (.variable 0)))
    (.zero (r + r))

/-- Failure of left additive cancellation in the radius `r+r` sort. -/
def negAddFormula (r : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius
      (![r] : BallContext 1) :=
  .distance
    (.add (.neg (.variable 0)) (.variable 0))
    (.zero (r + r))

def addNegSentence (r : ℚ≥0) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup r (addNegFormula r)

def negAddSentence (r : ℚ≥0) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup r (negAddFormula r)

theorem addNegFormula_realize (r : ℚ≥0)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r] : BallContext 1)) :
    (addNegFormula r).realize expansionStructure assignment =
      zeroTruthValue := by
  apply Subtype.ext
  change dist ((assignment 0).1 + -((assignment 0).1)) 0 /
      rationalBallMetricBound (r + r) = 0
  simp

theorem negAddFormula_realize (r : ℚ≥0)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r] : BallContext 1)) :
    (negAddFormula r).realize expansionStructure assignment =
      zeroTruthValue := by
  apply Subtype.ext
  change dist (-((assignment 0).1) + (assignment 0).1) 0 /
      rationalBallMetricBound (r + r) = 0
  simp

@[simp] theorem addNegSentence_value (r : ℚ≥0) :
    (addNegSentence r).value expansionStructure = zeroTruthValue := by
  change (⨆ x : expansionStructure.Ball r,
      (addNegFormula r).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) = zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun x ↦
      (addNegFormula_realize r
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).le
  · exact ((⨆ x : expansionStructure.Ball r,
      (addNegFormula r).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) : TruthValue).2.1

@[simp] theorem negAddSentence_value (r : ℚ≥0) :
    (negAddSentence r).value expansionStructure = zeroTruthValue := by
  change (⨆ x : expansionStructure.Ball r,
      (negAddFormula r).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) = zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun x ↦
      (negAddFormula_realize r
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).le
  · exact ((⨆ x : expansionStructure.Ball r,
      (negAddFormula r).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) : TruthValue).2.1

theorem dist_add_neg_eq_zero_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    (r : ℚ≥0) (x : M.Ball r) :
    dist (M.add r r (x, M.neg r x)) (M.zero (r + r)) = 0 := by
  have hsentence : (addNegSentence r).value M = zeroTruthValue := by
    calc
      (addNegSentence r).value M =
          (addNegSentence r).value expansionStructure :=
        (hTheory (addNegSentence r)).symm
      _ = zeroTruthValue := addNegSentence_value r
  have hle := realize_le_unarySentence M r (addNegFormula r) x
  change (addNegFormula r).realize M _ ≤
    (addNegSentence r).value M at hle
  rw [hsentence] at hle
  have hzero : (addNegFormula r).realize M
      (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) = zeroTruthValue :=
    le_antisymm hle
      ((addNegFormula r).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).2.1
  have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) hzero
  change dist (M.add r r (x, M.neg r x)) (M.zero (r + r)) /
      M.sortBound (r + r) = 0 at hcoe
  exact (div_eq_zero_iff.mp hcoe).resolve_right
    (ne_of_gt (M.sortBound_pos (r + r)))

theorem dist_neg_add_eq_zero_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    (r : ℚ≥0) (x : M.Ball r) :
    dist (M.add r r (M.neg r x, x)) (M.zero (r + r)) = 0 := by
  have hsentence : (negAddSentence r).value M = zeroTruthValue := by
    calc
      (negAddSentence r).value M =
          (negAddSentence r).value expansionStructure :=
        (hTheory (negAddSentence r)).symm
      _ = zeroTruthValue := negAddSentence_value r
  have hle := realize_le_unarySentence M r (negAddFormula r) x
  change (negAddFormula r).realize M _ ≤
    (negAddSentence r).value M at hle
  rw [hsentence] at hle
  have hzero : (negAddFormula r).realize M
      (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) = zeroTruthValue :=
    le_antisymm hle
      ((negAddFormula r).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).2.1
  have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) hzero
  change dist (M.add r r (M.neg r x, x)) (M.zero (r + r)) /
      M.sortBound (r + r) = 0 at hcoe
  exact (div_eq_zero_iff.mp hcoe).resolve_right
    (ne_of_gt (M.sortBound_pos (r + r)))

/-- Common comparison radius for the two orders of a binary sum. -/
def addCommTarget (r s : ℚ≥0) : ℚ≥0 :=
  (r + s) + (s + r)

/-- Failure of commutativity after both sums are included into a common
radius sort. -/
def addCommFormula (r s : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius
      (![r, s] : BallContext 2) :=
  .distance
    (.inclusion (le_add_of_nonneg_right (zero_le (s + r)))
      (.add (.variable 0) (.variable 1)))
    (.inclusion (le_add_of_nonneg_left (zero_le (r + s)))
      (.add (.variable 1) (.variable 0)))

def addCommSentence (r s : ℚ≥0) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup s (.iSup r (addCommFormula r s))

theorem realize_le_addCommSentence
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (r s : ℚ≥0) (x : M.Ball r) (y : M.Ball s) :
    (addCommFormula r s).realize M
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) ≤
      (addCommSentence r s).value M := by
  apply le_trans
  · exact le_iSup
      (fun z : M.Ball r ↦
        (addCommFormula r s).realize M
          (Fin.cons z (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) x
  · exact le_iSup
      (fun z : M.Ball s ↦ ⨆ w : M.Ball r,
        (addCommFormula r s).realize M
          (Fin.cons w (Fin.cons z (fun i : Fin 0 ↦ nomatch i)))) y

theorem addCommFormula_realize (r s : ℚ≥0)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r, s] : BallContext 2)) :
    (addCommFormula r s).realize expansionStructure assignment =
      zeroTruthValue := by
  apply Subtype.ext
  change dist ((assignment 0).1 + (assignment 1).1)
      ((assignment 1).1 + (assignment 0).1) /
        rationalBallMetricBound (addCommTarget r s) = 0
  rw [add_comm]
  simp

@[simp] theorem addCommSentence_value (r s : ℚ≥0) :
    (addCommSentence r s).value expansionStructure = zeroTruthValue := by
  change (⨆ y : expansionStructure.Ball s,
      ⨆ x : expansionStructure.Ball r,
        (addCommFormula r s).realize expansionStructure
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) =
    zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun y ↦ iSup_le fun x ↦
      (addCommFormula_realize r s
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))).le
  · exact ((⨆ y : expansionStructure.Ball s,
      ⨆ x : expansionStructure.Ball r,
        (addCommFormula r s).realize expansionStructure
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) :
      TruthValue).2.1

theorem dist_add_comm_eq_zero_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    (r s : ℚ≥0) (x : M.Ball r) (y : M.Ball s) :
    dist
        (M.inclusion (le_add_of_nonneg_right (zero_le (s + r)))
          (M.add r s (x, y)))
        (M.inclusion (le_add_of_nonneg_left (zero_le (r + s)))
          (M.add s r (y, x))) = 0 := by
  have hsentence : (addCommSentence r s).value M = zeroTruthValue := by
    calc
      (addCommSentence r s).value M =
          (addCommSentence r s).value expansionStructure :=
        (hTheory (addCommSentence r s)).symm
      _ = zeroTruthValue := addCommSentence_value r s
  have hle := realize_le_addCommSentence M r s x y
  rw [hsentence] at hle
  have hzero : (addCommFormula r s).realize M
      (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) =
        zeroTruthValue :=
    le_antisymm hle
      ((addCommFormula r s).realize M
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))).2.1
  have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) hzero
  change dist
      (M.inclusion (le_add_of_nonneg_right (zero_le (s + r)))
        (M.add r s (x, y)))
      (M.inclusion (le_add_of_nonneg_left (zero_le (r + s)))
        (M.add s r (y, x))) / M.sortBound (addCommTarget r s) = 0 at hcoe
  exact (div_eq_zero_iff.mp hcoe).resolve_right
    (ne_of_gt (M.sortBound_pos (addCommTarget r s)))

/-- Common comparison radius for the two parenthesizations of a triple sum. -/
def addAssocTarget (r s t : ℚ≥0) : ℚ≥0 :=
  ((r + s) + t) + (r + (s + t))

/-- Failure of associativity after both triple sums are included into one
common radius sort. -/
def addAssocFormula (r s t : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius
      (![r, s, t] : BallContext 3) :=
  .distance
    (.inclusion (le_add_of_nonneg_right (zero_le (r + (s + t))))
      (.add (.add (.variable 0) (.variable 1)) (.variable 2)))
    (.inclusion (le_add_of_nonneg_left (zero_le ((r + s) + t)))
      (.add (.variable 0) (.add (.variable 1) (.variable 2))))

def addAssocSentence (r s t : ℚ≥0) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup t (.iSup s (.iSup r (addAssocFormula r s t)))

theorem realize_le_addAssocSentence
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (r s t : ℚ≥0) (x : M.Ball r) (y : M.Ball s) (z : M.Ball t) :
    (addAssocFormula r s t).realize M
        (Fin.cons x (Fin.cons y (Fin.cons z
          (fun i : Fin 0 ↦ nomatch i)))) ≤
      (addAssocSentence r s t).value M := by
  apply le_trans
  · exact le_iSup
      (fun w : M.Ball r ↦
        (addAssocFormula r s t).realize M
          (Fin.cons w (Fin.cons y (Fin.cons z
            (fun i : Fin 0 ↦ nomatch i))))) x
  · apply le_trans
    · exact le_iSup
        (fun w : M.Ball s ↦ ⨆ v : M.Ball r,
          (addAssocFormula r s t).realize M
            (Fin.cons v (Fin.cons w (Fin.cons z
              (fun i : Fin 0 ↦ nomatch i))))) y
    · exact le_iSup
        (fun w : M.Ball t ↦ ⨆ v : M.Ball s, ⨆ u : M.Ball r,
          (addAssocFormula r s t).realize M
            (Fin.cons u (Fin.cons v (Fin.cons w
              (fun i : Fin 0 ↦ nomatch i))))) z

theorem addAssocFormula_realize (r s t : ℚ≥0)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r, s, t] : BallContext 3)) :
    (addAssocFormula r s t).realize expansionStructure assignment =
      zeroTruthValue := by
  apply Subtype.ext
  change dist (((assignment 0).1 + (assignment 1).1) + (assignment 2).1)
      ((assignment 0).1 + ((assignment 1).1 + (assignment 2).1)) /
        rationalBallMetricBound (addAssocTarget r s t) = 0
  rw [add_assoc]
  simp

@[simp] theorem addAssocSentence_value (r s t : ℚ≥0) :
    (addAssocSentence r s t).value expansionStructure = zeroTruthValue := by
  change (⨆ z : expansionStructure.Ball t,
      ⨆ y : expansionStructure.Ball s,
      ⨆ x : expansionStructure.Ball r,
        (addAssocFormula r s t).realize expansionStructure
          (Fin.cons x (Fin.cons y (Fin.cons z
            (fun i : Fin 0 ↦ nomatch i))))) = zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun z ↦ iSup_le fun y ↦ iSup_le fun x ↦
      (addAssocFormula_realize r s t
        (Fin.cons x (Fin.cons y (Fin.cons z
          (fun i : Fin 0 ↦ nomatch i))))).le
  · exact ((⨆ z : expansionStructure.Ball t,
      ⨆ y : expansionStructure.Ball s,
      ⨆ x : expansionStructure.Ball r,
        (addAssocFormula r s t).realize expansionStructure
          (Fin.cons x (Fin.cons y (Fin.cons z
            (fun i : Fin 0 ↦ nomatch i))))) : TruthValue).2.1

theorem dist_add_assoc_eq_zero_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    (r s t : ℚ≥0) (x : M.Ball r) (y : M.Ball s) (z : M.Ball t) :
    dist
        (M.inclusion (le_add_of_nonneg_right (zero_le (r + (s + t))))
          (M.add (r + s) t (M.add r s (x, y), z)))
        (M.inclusion (le_add_of_nonneg_left (zero_le ((r + s) + t)))
          (M.add r (s + t) (x, M.add s t (y, z)))) = 0 := by
  have hsentence :
      (addAssocSentence r s t).value M = zeroTruthValue := by
    calc
      (addAssocSentence r s t).value M =
          (addAssocSentence r s t).value expansionStructure :=
        (hTheory (addAssocSentence r s t)).symm
      _ = zeroTruthValue := addAssocSentence_value r s t
  have hle := realize_le_addAssocSentence M r s t x y z
  rw [hsentence] at hle
  have hzero : (addAssocFormula r s t).realize M
      (Fin.cons x (Fin.cons y (Fin.cons z
        (fun i : Fin 0 ↦ nomatch i)))) = zeroTruthValue :=
    le_antisymm hle
      ((addAssocFormula r s t).realize M
        (Fin.cons x (Fin.cons y (Fin.cons z
          (fun i : Fin 0 ↦ nomatch i))))).2.1
  have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) hzero
  change dist
      (M.inclusion (le_add_of_nonneg_right (zero_le (r + (s + t))))
        (M.add (r + s) t (M.add r s (x, y), z)))
      (M.inclusion (le_add_of_nonneg_left (zero_le ((r + s) + t)))
        (M.add r (s + t) (x, M.add s t (y, z)))) /
          M.sortBound (addAssocTarget r s t) = 0 at hcoe
  exact (div_eq_zero_iff.mp hcoe).resolve_right
    (ne_of_gt (M.sortBound_pos (addAssocTarget r s t)))

/-! ## Rational scalar identities -/

/-- Common comparison radius for `1 • x` and `x`. -/
def oneSmulTarget (r : ℚ≥0) : ℚ≥0 :=
  (1 : ℚ).nnabs * r + r

/-- Failure of scalar identity after both terms are included into a common
radius sort. -/
def oneSmulFormula (r : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius
      (![r] : BallContext 1) :=
  .distance
    (.inclusion (le_add_of_nonneg_right (zero_le r))
      (.smul 1 (.variable 0)))
    (.inclusion (le_add_of_nonneg_left
      (zero_le ((1 : ℚ).nnabs * r))) (.variable 0))

def oneSmulSentence (r : ℚ≥0) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup r (oneSmulFormula r)

theorem oneSmulFormula_realize (r : ℚ≥0)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r] : BallContext 1)) :
    (oneSmulFormula r).realize expansionStructure assignment =
      zeroTruthValue := by
  apply Subtype.ext
  change dist (((1 : ℚ) : ℝ) • (assignment 0).1) (assignment 0).1 /
      rationalBallMetricBound (oneSmulTarget r) = 0
  simp

@[simp] theorem oneSmulSentence_value (r : ℚ≥0) :
    (oneSmulSentence r).value expansionStructure = zeroTruthValue := by
  change (⨆ x : expansionStructure.Ball r,
      (oneSmulFormula r).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) = zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun x ↦
      (oneSmulFormula_realize r
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).le
  · exact ((⨆ x : expansionStructure.Ball r,
      (oneSmulFormula r).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) : TruthValue).2.1

theorem dist_one_smul_eq_zero_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    (r : ℚ≥0) (x : M.Ball r) :
    dist
        (M.inclusion (le_add_of_nonneg_right (zero_le r))
          (M.smul 1 r x))
        (M.inclusion (le_add_of_nonneg_left
          (zero_le ((1 : ℚ).nnabs * r))) x) = 0 := by
  have hsentence : (oneSmulSentence r).value M = zeroTruthValue := by
    calc
      (oneSmulSentence r).value M =
          (oneSmulSentence r).value expansionStructure :=
        (hTheory (oneSmulSentence r)).symm
      _ = zeroTruthValue := oneSmulSentence_value r
  have hle := realize_le_unarySentence M r (oneSmulFormula r) x
  change (oneSmulFormula r).realize M _ ≤
    (oneSmulSentence r).value M at hle
  rw [hsentence] at hle
  have hzero : (oneSmulFormula r).realize M
      (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) = zeroTruthValue :=
    le_antisymm hle
      ((oneSmulFormula r).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).2.1
  have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) hzero
  change dist
      (M.inclusion (le_add_of_nonneg_right (zero_le r)) (M.smul 1 r x))
      (M.inclusion (le_add_of_nonneg_left
        (zero_le ((1 : ℚ).nnabs * r))) x) /
          M.sortBound (oneSmulTarget r) = 0 at hcoe
  exact (div_eq_zero_iff.mp hcoe).resolve_right
    (ne_of_gt (M.sortBound_pos (oneSmulTarget r)))

/-- Common comparison radius for `(q*p) • x` and `q • (p • x)`. -/
def mulSmulTarget (q p : ℚ) (r : ℚ≥0) : ℚ≥0 :=
  (q * p).nnabs * r + q.nnabs * (p.nnabs * r)

/-- Failure of scalar composition after both terms are included into a
common radius sort. -/
def mulSmulFormula (q p : ℚ) (r : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius
      (![r] : BallContext 1) :=
  .distance
    (.inclusion
      (le_add_of_nonneg_right (zero_le (q.nnabs * (p.nnabs * r))))
      (.smul (q * p) (.variable 0)))
    (.inclusion
      (le_add_of_nonneg_left (zero_le ((q * p).nnabs * r)))
      (.smul q (.smul p (.variable 0))))

def mulSmulSentence (q p : ℚ) (r : ℚ≥0) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup r (mulSmulFormula q p r)

theorem mulSmulFormula_realize (q p : ℚ) (r : ℚ≥0)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r] : BallContext 1)) :
    (mulSmulFormula q p r).realize expansionStructure assignment =
      zeroTruthValue := by
  apply Subtype.ext
  change dist (((q * p : ℚ) : ℝ) • (assignment 0).1)
      ((q : ℝ) • ((p : ℝ) • (assignment 0).1)) /
        rationalBallMetricBound (mulSmulTarget q p r) = 0
  simp [mul_smul]

@[simp] theorem mulSmulSentence_value (q p : ℚ) (r : ℚ≥0) :
    (mulSmulSentence q p r).value expansionStructure = zeroTruthValue := by
  change (⨆ x : expansionStructure.Ball r,
      (mulSmulFormula q p r).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) = zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun x ↦
      (mulSmulFormula_realize q p r
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).le
  · exact ((⨆ x : expansionStructure.Ball r,
      (mulSmulFormula q p r).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) : TruthValue).2.1

theorem dist_mul_smul_eq_zero_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    (q p : ℚ) (r : ℚ≥0) (x : M.Ball r) :
    dist
        (M.inclusion
          (le_add_of_nonneg_right (zero_le (q.nnabs * (p.nnabs * r))))
          (M.smul (q * p) r x))
        (M.inclusion
          (le_add_of_nonneg_left (zero_le ((q * p).nnabs * r)))
          (M.smul q (p.nnabs * r) (M.smul p r x))) = 0 := by
  have hsentence :
      (mulSmulSentence q p r).value M = zeroTruthValue := by
    calc
      (mulSmulSentence q p r).value M =
          (mulSmulSentence q p r).value expansionStructure :=
        (hTheory (mulSmulSentence q p r)).symm
      _ = zeroTruthValue := mulSmulSentence_value q p r
  have hle := realize_le_unarySentence M r (mulSmulFormula q p r) x
  change (mulSmulFormula q p r).realize M _ ≤
    (mulSmulSentence q p r).value M at hle
  rw [hsentence] at hle
  have hzero : (mulSmulFormula q p r).realize M
      (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) = zeroTruthValue :=
    le_antisymm hle
      ((mulSmulFormula q p r).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).2.1
  have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) hzero
  change dist
      (M.inclusion
        (le_add_of_nonneg_right (zero_le (q.nnabs * (p.nnabs * r))))
        (M.smul (q * p) r x))
      (M.inclusion
        (le_add_of_nonneg_left (zero_le ((q * p).nnabs * r)))
        (M.smul q (p.nnabs * r) (M.smul p r x))) /
          M.sortBound (mulSmulTarget q p r) = 0 at hcoe
  exact (div_eq_zero_iff.mp hcoe).resolve_right
    (ne_of_gt (M.sortBound_pos (mulSmulTarget q p r)))

/-- Common comparison radius for `q • (x + y)` and `q • x + q • y`. -/
def smulAddTarget (q : ℚ) (r s : ℚ≥0) : ℚ≥0 :=
  q.nnabs * (r + s) + (q.nnabs * r + q.nnabs * s)

/-- Failure of scalar multiplication to distribute over vector addition,
after both terms are included into a common radius sort. -/
def smulAddFormula (q : ℚ) (r s : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius
      (![r, s] : BallContext 2) :=
  .distance
    (.inclusion
      (le_add_of_nonneg_right (zero_le (q.nnabs * r + q.nnabs * s)))
      (.smul q (.add (.variable 0) (.variable 1))))
    (.inclusion
      (le_add_of_nonneg_left (zero_le (q.nnabs * (r + s))))
      (.add (.smul q (.variable 0)) (.smul q (.variable 1))))

def smulAddSentence (q : ℚ) (r s : ℚ≥0) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup s (.iSup r (smulAddFormula q r s))

theorem realize_le_smulAddSentence
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (q : ℚ) (r s : ℚ≥0) (x : M.Ball r) (y : M.Ball s) :
    (smulAddFormula q r s).realize M
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) ≤
      (smulAddSentence q r s).value M := by
  apply le_trans
  · exact le_iSup
      (fun z : M.Ball r ↦
        (smulAddFormula q r s).realize M
          (Fin.cons z (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) x
  · exact le_iSup
      (fun z : M.Ball s ↦ ⨆ w : M.Ball r,
        (smulAddFormula q r s).realize M
          (Fin.cons w (Fin.cons z (fun i : Fin 0 ↦ nomatch i)))) y

theorem smulAddFormula_realize (q : ℚ) (r s : ℚ≥0)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r, s] : BallContext 2)) :
    (smulAddFormula q r s).realize expansionStructure assignment =
      zeroTruthValue := by
  apply Subtype.ext
  change dist
      ((q : ℝ) • ((assignment 0).1 + (assignment 1).1))
      (((q : ℝ) • (assignment 0).1) +
        ((q : ℝ) • (assignment 1).1)) /
        rationalBallMetricBound (smulAddTarget q r s) = 0
  simp [smul_add]

@[simp] theorem smulAddSentence_value (q : ℚ) (r s : ℚ≥0) :
    (smulAddSentence q r s).value expansionStructure = zeroTruthValue := by
  change (⨆ y : expansionStructure.Ball s,
      ⨆ x : expansionStructure.Ball r,
        (smulAddFormula q r s).realize expansionStructure
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) =
    zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun y ↦ iSup_le fun x ↦
      (smulAddFormula_realize q r s
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))).le
  · exact ((⨆ y : expansionStructure.Ball s,
      ⨆ x : expansionStructure.Ball r,
        (smulAddFormula q r s).realize expansionStructure
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) :
      TruthValue).2.1

theorem dist_smul_add_eq_zero_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    (q : ℚ) (r s : ℚ≥0) (x : M.Ball r) (y : M.Ball s) :
    dist
        (M.inclusion
          (le_add_of_nonneg_right (zero_le (q.nnabs * r + q.nnabs * s)))
          (M.smul q (r + s) (M.add r s (x, y))))
        (M.inclusion
          (le_add_of_nonneg_left (zero_le (q.nnabs * (r + s))))
          (M.add (q.nnabs * r) (q.nnabs * s)
            (M.smul q r x, M.smul q s y))) = 0 := by
  have hsentence :
      (smulAddSentence q r s).value M = zeroTruthValue := by
    calc
      (smulAddSentence q r s).value M =
          (smulAddSentence q r s).value expansionStructure :=
        (hTheory (smulAddSentence q r s)).symm
      _ = zeroTruthValue := smulAddSentence_value q r s
  have hle := realize_le_smulAddSentence M q r s x y
  rw [hsentence] at hle
  have hzero : (smulAddFormula q r s).realize M
      (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) =
        zeroTruthValue :=
    le_antisymm hle
      ((smulAddFormula q r s).realize M
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))).2.1
  have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) hzero
  change dist
      (M.inclusion
        (le_add_of_nonneg_right (zero_le (q.nnabs * r + q.nnabs * s)))
        (M.smul q (r + s) (M.add r s (x, y))))
      (M.inclusion
        (le_add_of_nonneg_left (zero_le (q.nnabs * (r + s))))
        (M.add (q.nnabs * r) (q.nnabs * s)
          (M.smul q r x, M.smul q s y))) /
          M.sortBound (smulAddTarget q r s) = 0 at hcoe
  exact (div_eq_zero_iff.mp hcoe).resolve_right
    (ne_of_gt (M.sortBound_pos (smulAddTarget q r s)))

/-- Common comparison radius for `(q + p) • x` and `q • x + p • x`. -/
def addSmulTarget (q p : ℚ) (r : ℚ≥0) : ℚ≥0 :=
  (q + p).nnabs * r + (q.nnabs * r + p.nnabs * r)

/-- Failure of rational scalar addition to distribute over a vector, after
both terms are included into a common radius sort. -/
def addSmulFormula (q p : ℚ) (r : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius
      (![r] : BallContext 1) :=
  .distance
    (.inclusion
      (le_add_of_nonneg_right (zero_le (q.nnabs * r + p.nnabs * r)))
      (.smul (q + p) (.variable 0)))
    (.inclusion
      (le_add_of_nonneg_left (zero_le ((q + p).nnabs * r)))
      (.add (.smul q (.variable 0)) (.smul p (.variable 0))))

def addSmulSentence (q p : ℚ) (r : ℚ≥0) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup r (addSmulFormula q p r)

theorem addSmulFormula_realize (q p : ℚ) (r : ℚ≥0)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r] : BallContext 1)) :
    (addSmulFormula q p r).realize expansionStructure assignment =
      zeroTruthValue := by
  apply Subtype.ext
  change dist
      (((q + p : ℚ) : ℝ) • (assignment 0).1)
      (((q : ℝ) • (assignment 0).1) +
        ((p : ℝ) • (assignment 0).1)) /
        rationalBallMetricBound (addSmulTarget q p r) = 0
  norm_cast
  simp [add_smul]

@[simp] theorem addSmulSentence_value (q p : ℚ) (r : ℚ≥0) :
    (addSmulSentence q p r).value expansionStructure = zeroTruthValue := by
  change (⨆ x : expansionStructure.Ball r,
      (addSmulFormula q p r).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) = zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun x ↦
      (addSmulFormula_realize q p r
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).le
  · exact ((⨆ x : expansionStructure.Ball r,
      (addSmulFormula q p r).realize expansionStructure
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))) : TruthValue).2.1

theorem dist_add_smul_eq_zero_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    (q p : ℚ) (r : ℚ≥0) (x : M.Ball r) :
    dist
        (M.inclusion
          (le_add_of_nonneg_right (zero_le (q.nnabs * r + p.nnabs * r)))
          (M.smul (q + p) r x))
        (M.inclusion
          (le_add_of_nonneg_left (zero_le ((q + p).nnabs * r)))
          (M.add (q.nnabs * r) (p.nnabs * r)
            (M.smul q r x, M.smul p r x))) = 0 := by
  have hsentence :
      (addSmulSentence q p r).value M = zeroTruthValue := by
    calc
      (addSmulSentence q p r).value M =
          (addSmulSentence q p r).value expansionStructure :=
        (hTheory (addSmulSentence q p r)).symm
      _ = zeroTruthValue := addSmulSentence_value q p r
  have hle := realize_le_unarySentence M r (addSmulFormula q p r) x
  change (addSmulFormula q p r).realize M _ ≤
    (addSmulSentence q p r).value M at hle
  rw [hsentence] at hle
  have hzero : (addSmulFormula q p r).realize M
      (Fin.cons x (fun i : Fin 0 ↦ nomatch i)) = zeroTruthValue :=
    le_antisymm hle
      ((addSmulFormula q p r).realize M
        (Fin.cons x (fun i : Fin 0 ↦ nomatch i))).2.1
  have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) hzero
  change dist
      (M.inclusion
        (le_add_of_nonneg_right (zero_le (q.nnabs * r + p.nnabs * r)))
        (M.smul (q + p) r x))
      (M.inclusion
        (le_add_of_nonneg_left (zero_le ((q + p).nnabs * r)))
        (M.add (q.nnabs * r) (p.nnabs * r)
          (M.smul q r x, M.smul p r x))) /
          M.sortBound (addSmulTarget q p r) = 0 at hcoe
  exact (div_eq_zero_iff.mp hcoe).resolve_right
    (ne_of_gt (M.sortBound_pos (addSmulTarget q p r)))

/-! ## Metric compatibility of addition -/

/-- Scale converting normalized distance in the radius-`r` sort to
normalized distance after translation into the radius-`r+s` sort. -/
def addRightDistanceScale (r s : ℚ≥0) : ℝ :=
  rationalBallMetricBound r / rationalBallMetricBound (r + s)

theorem addRightDistanceScale_nonneg (r s : ℚ≥0) :
    0 ≤ addRightDistanceScale r s :=
  div_nonneg (rationalBallMetricBound_pos r).le
    (rationalBallMetricBound_pos (r + s)).le

theorem addRightDistanceScale_le_one (r s : ℚ≥0) :
    addRightDistanceScale r s ≤ 1 := by
  apply (div_le_one (rationalBallMetricBound_pos (r + s))).2
  exact rationalBallMetricBound_mono
    (le_add_of_nonneg_right (zero_le s))

/-- Failure of right translation to preserve the normalization-corrected
distance. -/
def addRightDistanceFormula (r s : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius
      (![r, r, s] : BallContext 3) :=
  .connective
    (scaledAbsoluteDifferenceConnective
      (addRightDistanceScale r s)
      (addRightDistanceScale_nonneg r s)
      (addRightDistanceScale_le_one r s))
    ![
      .distance
        (.add (.variable 0) (.variable 2))
        (.add (.variable 1) (.variable 2)),
      .distance (.variable 0) (.variable 1)]

def addRightDistanceSentence (r s : ℚ≥0) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup s (.iSup r (.iSup r (addRightDistanceFormula r s)))

theorem realize_le_addRightDistanceSentence
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (r s : ℚ≥0) (x y : M.Ball r) (z : M.Ball s) :
    (addRightDistanceFormula r s).realize M
        (Fin.cons x (Fin.cons y (Fin.cons z
          (fun i : Fin 0 ↦ nomatch i)))) ≤
      (addRightDistanceSentence r s).value M := by
  apply le_trans
  · exact le_iSup
      (fun w : M.Ball r ↦
        (addRightDistanceFormula r s).realize M
          (Fin.cons w (Fin.cons y (Fin.cons z
            (fun i : Fin 0 ↦ nomatch i))))) x
  · apply le_trans
    · exact le_iSup
        (fun w : M.Ball r ↦ ⨆ v : M.Ball r,
          (addRightDistanceFormula r s).realize M
            (Fin.cons v (Fin.cons w (Fin.cons z
              (fun i : Fin 0 ↦ nomatch i))))) y
    · exact le_iSup
        (fun w : M.Ball s ↦ ⨆ v : M.Ball r, ⨆ u : M.Ball r,
          (addRightDistanceFormula r s).realize M
            (Fin.cons u (Fin.cons v (Fin.cons w
              (fun i : Fin 0 ↦ nomatch i))))) z

theorem addRightDistanceFormula_realize (r s : ℚ≥0)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r, r, s] : BallContext 3)) :
    (addRightDistanceFormula r s).realize expansionStructure assignment =
      zeroTruthValue := by
  apply (scaledAbsoluteDifferenceConnective_eq_zero_iff _ _ _ _).2
  change dist ((assignment 0).1 + (assignment 2).1)
        ((assignment 1).1 + (assignment 2).1) /
      rationalBallMetricBound (r + s) =
    addRightDistanceScale r s *
      (dist (assignment 0).1 (assignment 1).1 /
        rationalBallMetricBound r)
  rw [dist_add_right]
  unfold addRightDistanceScale
  field_simp [ne_of_gt (rationalBallMetricBound_pos r),
    ne_of_gt (rationalBallMetricBound_pos (r + s))]

@[simp] theorem addRightDistanceSentence_value (r s : ℚ≥0) :
    (addRightDistanceSentence r s).value expansionStructure =
      zeroTruthValue := by
  change (⨆ z : expansionStructure.Ball s,
      ⨆ y : expansionStructure.Ball r,
      ⨆ x : expansionStructure.Ball r,
        (addRightDistanceFormula r s).realize expansionStructure
          (Fin.cons x (Fin.cons y (Fin.cons z
            (fun i : Fin 0 ↦ nomatch i))))) = zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun z ↦ iSup_le fun y ↦ iSup_le fun x ↦
      (addRightDistanceFormula_realize r s
        (Fin.cons x (Fin.cons y (Fin.cons z
          (fun i : Fin 0 ↦ nomatch i))))).le
  · exact ((⨆ z : expansionStructure.Ball s,
      ⨆ y : expansionStructure.Ball r,
      ⨆ x : expansionStructure.Ball r,
        (addRightDistanceFormula r s).realize expansionStructure
          (Fin.cons x (Fin.cons y (Fin.cons z
            (fun i : Fin 0 ↦ nomatch i))))) : TruthValue).2.1

/-- In every model of the complete typed X theory, right translation
preserves the reconstruction's normalization-corrected distance. -/
theorem addition_preserves_rescaledDistance_right_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    (r s : ℚ≥0) (x y : M.Ball r) (z : M.Ball s) :
    rationalBallMetricBound (r + s) *
        (dist (M.add r s (x, z)) (M.add r s (y, z)) /
          M.sortBound (r + s)) =
      rationalBallMetricBound r * (dist x y / M.sortBound r) := by
  have hsentence :
      (addRightDistanceSentence r s).value M = zeroTruthValue := by
    calc
      (addRightDistanceSentence r s).value M =
          (addRightDistanceSentence r s).value expansionStructure :=
        (hTheory (addRightDistanceSentence r s)).symm
      _ = zeroTruthValue := addRightDistanceSentence_value r s
  have hle := realize_le_addRightDistanceSentence M r s x y z
  rw [hsentence] at hle
  have hzero : (addRightDistanceFormula r s).realize M
      (Fin.cons x (Fin.cons y (Fin.cons z
        (fun i : Fin 0 ↦ nomatch i)))) = zeroTruthValue :=
    le_antisymm hle
      ((addRightDistanceFormula r s).realize M
        (Fin.cons x (Fin.cons y (Fin.cons z
          (fun i : Fin 0 ↦ nomatch i))))).2.1
  have hscaled :=
    (scaledAbsoluteDifferenceConnective_eq_zero_iff
      (addRightDistanceScale r s)
      (addRightDistanceScale_nonneg r s)
      (addRightDistanceScale_le_one r s) _).1 hzero
  change dist (M.add r s (x, z)) (M.add r s (y, z)) /
      M.sortBound (r + s) =
    addRightDistanceScale r s * (dist x y / M.sortBound r) at hscaled
  rw [hscaled]
  unfold addRightDistanceScale
  field_simp [ne_of_gt (rationalBallMetricBound_pos (r + s))]

/-! ## Metric compatibility of rational scalar multiplication -/

/-- Coefficient converting normalized input distance into the sharp upper
bound for normalized distance after multiplication by `q`. -/
def smulDistanceScale (q : ℚ) (r : ℚ≥0) : ℝ :=
  (q.nnabs : ℝ) * rationalBallMetricBound r /
    rationalBallMetricBound (q.nnabs * r)

theorem smulDistanceScale_nonneg (q : ℚ) (r : ℚ≥0) :
    0 ≤ smulDistanceScale q r := by
  exact div_nonneg
    (mul_nonneg (NNRat.cast_nonneg q.nnabs)
      (rationalBallMetricBound_pos r).le)
    (rationalBallMetricBound_pos (q.nnabs * r)).le

/-- Failure of multiplication by `q` to satisfy its sharp reconstructed
distance bound. -/
def smulDistanceFormula (q : ℚ) (r : ℚ≥0) :
    BallFormula PredicateSymbol predicateRadius
      (![r, r] : BallContext 2) :=
  .connective
    (scaledOrderViolationConnective
      (smulDistanceScale q r) (smulDistanceScale_nonneg q r))
    ![
      .distance (.smul q (.variable 0)) (.smul q (.variable 1)),
      .distance (.variable 0) (.variable 1)]

def smulDistanceSentence (q : ℚ) (r : ℚ≥0) :
    BallSentence PredicateSymbol predicateRadius :=
  .iSup r (.iSup r (smulDistanceFormula q r))

theorem realize_le_smulDistanceSentence
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (q : ℚ) (r : ℚ≥0) (x y : M.Ball r) :
    (smulDistanceFormula q r).realize M
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) ≤
      (smulDistanceSentence q r).value M := by
  apply le_trans
  · exact le_iSup
      (fun z : M.Ball r ↦
        (smulDistanceFormula q r).realize M
          (Fin.cons z (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) x
  · exact le_iSup
      (fun z : M.Ball r ↦ ⨆ w : M.Ball r,
        (smulDistanceFormula q r).realize M
          (Fin.cons w (Fin.cons z (fun i : Fin 0 ↦ nomatch i)))) y

theorem smulDistanceFormula_realize (q : ℚ) (r : ℚ≥0)
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![r, r] : BallContext 2)) :
    (smulDistanceFormula q r).realize expansionStructure assignment =
      zeroTruthValue := by
  apply (scaledOrderViolationConnective_eq_zero_iff _ _ _).2
  change dist ((q : ℝ) • (assignment 0).1)
        ((q : ℝ) • (assignment 1).1) /
      rationalBallMetricBound (q.nnabs * r) ≤
    smulDistanceScale q r *
      (dist (assignment 0).1 (assignment 1).1 /
        rationalBallMetricBound r)
  rw [dist_smul₀, Real.norm_eq_abs]
  have hq : |(q : ℝ)| = (q.nnabs : ℝ) := by norm_cast
  rw [hq]
  unfold smulDistanceScale
  field_simp [ne_of_gt (rationalBallMetricBound_pos r),
    ne_of_gt (rationalBallMetricBound_pos (q.nnabs * r))]
  exact le_rfl

@[simp] theorem smulDistanceSentence_value (q : ℚ) (r : ℚ≥0) :
    (smulDistanceSentence q r).value expansionStructure =
      zeroTruthValue := by
  change (⨆ y : expansionStructure.Ball r,
      ⨆ x : expansionStructure.Ball r,
        (smulDistanceFormula q r).realize expansionStructure
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) =
    zeroTruthValue
  apply le_antisymm
  · exact iSup_le fun y ↦ iSup_le fun x ↦
      (smulDistanceFormula_realize q r
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))).le
  · exact ((⨆ y : expansionStructure.Ball r,
      ⨆ x : expansionStructure.Ball r,
        (smulDistanceFormula q r).realize expansionStructure
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))) :
      TruthValue).2.1

/-- Every fixed rational scalar map satisfies its sharp reconstructed
distance bound in every model of the complete typed X theory. -/
theorem smul_rescaledDistance_le_of_sameCompleteTheory
    (M : BallStructure.{u} PredicateSymbol predicateRadius)
    (hTheory : BallSameCompleteTheory expansionStructure M)
    (q : ℚ) (r : ℚ≥0) (x y : M.Ball r) :
    rationalBallMetricBound (q.nnabs * r) *
        (dist (M.smul q r x) (M.smul q r y) /
          M.sortBound (q.nnabs * r)) ≤
      (q.nnabs : ℝ) *
        (rationalBallMetricBound r * (dist x y / M.sortBound r)) := by
  have hsentence :
      (smulDistanceSentence q r).value M = zeroTruthValue := by
    calc
      (smulDistanceSentence q r).value M =
          (smulDistanceSentence q r).value expansionStructure :=
        (hTheory (smulDistanceSentence q r)).symm
      _ = zeroTruthValue := smulDistanceSentence_value q r
  have hle := realize_le_smulDistanceSentence M q r x y
  rw [hsentence] at hle
  have hzero : (smulDistanceFormula q r).realize M
      (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) =
        zeroTruthValue :=
    le_antisymm hle
      ((smulDistanceFormula q r).realize M
        (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))).2.1
  have hscaled :=
    (scaledOrderViolationConnective_eq_zero_iff
      (smulDistanceScale q r) (smulDistanceScale_nonneg q r) _).1 hzero
  change dist (M.smul q r x) (M.smul q r y) /
      M.sortBound (q.nnabs * r) ≤
    smulDistanceScale q r * (dist x y / M.sortBound r) at hscaled
  calc
    rationalBallMetricBound (q.nnabs * r) *
        (dist (M.smul q r x) (M.smul q r y) /
          M.sortBound (q.nnabs * r)) ≤
      rationalBallMetricBound (q.nnabs * r) *
        (smulDistanceScale q r * (dist x y / M.sortBound r)) :=
      mul_le_mul_of_nonneg_left hscaled
        (rationalBallMetricBound_pos (q.nnabs * r)).le
    _ = (q.nnabs : ℝ) *
        (rationalBallMetricBound r * (dist x y / M.sortBound r)) := by
      unfold smulDistanceScale
      field_simp [ne_of_gt (rationalBallMetricBound_pos (q.nnabs * r))]

end

end NormFormula.X.BallLanguage
