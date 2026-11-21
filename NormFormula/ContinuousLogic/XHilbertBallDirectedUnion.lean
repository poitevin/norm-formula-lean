import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Instances.Rat
import NormFormula.ContinuousLogic.XHilbertBallCoherence
import NormFormula.ContinuousLogic.XHilbertBallSentences

/-!
# The directed union of an abstract X ball model

A model of the complete typed ball theory is bundled with its theory
equivalence to the distinguished X expansion.  A raw directed-union point is
a dependent pair of a rational radius and a point in that radius sort.

For two such points, their canonical distance is measured after including
them into a common radius and undoing that sort's semantic normalization by
the fixed language scale.  The main result of this file proves that the value
is unchanged when the common target radius is enlarged.  This is the key
well-definedness lemma for the forthcoming pseudometric and separation
quotient.
-/

namespace NormFormula.X.BallLanguage

noncomputable section

open NormFormula.ContinuousLogic
open Set TopologicalSpace

universe u

/-- A ball structure bundled with the assertion that it models the complete
typed theory of the distinguished X expansion. -/
structure XBallTheoryModel where
  model : BallStructure.{u} PredicateSymbol predicateRadius
  sameCompleteTheory : BallSameCompleteTheory expansionStructure model

namespace XBallTheoryModel

/-- The raw sigma-type union of all rational-radius sorts. -/
def DirectedPoint (A : XBallTheoryModel.{u}) :=
  Σ radius : ℚ≥0, A.model.Ball radius

/-- The normalization-correct distance between two raw points, measured in
an arbitrary common target radius. -/
def rescaledDistanceAt (A : XBallTheoryModel.{u})
    (x y : A.DirectedPoint) (target : ℚ≥0)
    (hx : x.1 ≤ target) (hy : y.1 ≤ target) : ℝ :=
  rationalBallMetricBound target *
    (dist (A.model.inclusion hx x.2) (A.model.inclusion hy y.2) /
      A.model.sortBound target)

theorem rescaledDistanceAt_nonneg (A : XBallTheoryModel.{u})
    (x y : A.DirectedPoint) (target : ℚ≥0)
    (hx : x.1 ≤ target) (hy : y.1 ≤ target) :
    0 ≤ A.rescaledDistanceAt x y target hx hy := by
  exact mul_nonneg (rationalBallMetricBound_pos target).le
    (div_nonneg dist_nonneg (A.model.sortBound_pos target).le)

theorem rescaledDistanceAt_self (A : XBallTheoryModel.{u})
    (x : A.DirectedPoint) (target : ℚ≥0) (hx : x.1 ≤ target) :
    A.rescaledDistanceAt x x target hx hx = 0 := by
  simp [rescaledDistanceAt]

/-- Replacing two composites of inclusions by the corresponding direct
inclusions does not change their target-sort distance. -/
theorem dist_compositeInclusions_eq_direct
    (A : XBallTheoryModel.{u}) (x y : A.DirectedPoint)
    {target larger : ℚ≥0}
    (hx : x.1 ≤ target) (hy : y.1 ≤ target) (h : target ≤ larger) :
    dist
        (A.model.inclusion h (A.model.inclusion hx x.2))
        (A.model.inclusion h (A.model.inclusion hy y.2)) =
      dist
        (A.model.inclusion (hx.trans h) x.2)
        (A.model.inclusion (hy.trans h) y.2) := by
  have hxzero := dist_inclusion_trans_eq_zero_of_sameCompleteTheory
    A.model A.sameCompleteTheory hx h x.2
  have hyzero := dist_inclusion_trans_eq_zero_of_sameCompleteTheory
    A.model A.sameCompleteTheory hy h y.2
  calc
    dist (A.model.inclusion h (A.model.inclusion hx x.2))
        (A.model.inclusion h (A.model.inclusion hy y.2)) =
      dist (A.model.inclusion (hx.trans h) x.2)
        (A.model.inclusion h (A.model.inclusion hy y.2)) := by
          rw [dist_comm]
          rw [PseudoMetricSpace.dist_eq_of_dist_zero _ hxzero]
          rw [dist_comm]
    _ = dist (A.model.inclusion (hx.trans h) x.2)
        (A.model.inclusion (hy.trans h) y.2) :=
      PseudoMetricSpace.dist_eq_of_dist_zero _ hyzero

/-- The normalization-correct distance is independent of enlarging the
chosen common target radius. -/
theorem rescaledDistanceAt_eq_of_le
    (A : XBallTheoryModel.{u}) (x y : A.DirectedPoint)
    {target larger : ℚ≥0}
    (hx : x.1 ≤ target) (hy : y.1 ≤ target) (h : target ≤ larger) :
    A.rescaledDistanceAt x y larger (hx.trans h) (hy.trans h) =
      A.rescaledDistanceAt x y target hx hy := by
  have hmetric := inclusion_preserves_rescaledDistance_of_sameCompleteTheory
    A.model A.sameCompleteTheory h
      (A.model.inclusion hx x.2) (A.model.inclusion hy y.2)
  unfold rescaledDistanceAt
  rw [← A.dist_compositeInclusions_eq_direct x y hx hy h]
  exact hmetric

/-- The canonical common radius assigned to two raw directed-union points. -/
def commonRadius (A : XBallTheoryModel.{u}) (x y : A.DirectedPoint) : ℚ≥0 :=
  x.1 + y.1

theorem left_le_commonRadius (A : XBallTheoryModel.{u})
    (x y : A.DirectedPoint) : x.1 ≤ A.commonRadius x y :=
  le_add_of_nonneg_right (zero_le y.1)

theorem right_le_commonRadius (A : XBallTheoryModel.{u})
    (x y : A.DirectedPoint) : y.1 ≤ A.commonRadius x y :=
  le_add_of_nonneg_left (zero_le x.1)

/-- The canonical raw directed-union distance, measured in the sum of the
two source radii. -/
def directedDistance (A : XBallTheoryModel.{u})
    (x y : A.DirectedPoint) : ℝ :=
  A.rescaledDistanceAt x y (A.commonRadius x y)
    (A.left_le_commonRadius x y) (A.right_le_commonRadius x y)

theorem directedDistance_nonneg (A : XBallTheoryModel.{u})
    (x y : A.DirectedPoint) : 0 ≤ A.directedDistance x y :=
  A.rescaledDistanceAt_nonneg x y _ _ _

theorem directedDistance_self (A : XBallTheoryModel.{u})
    (x : A.DirectedPoint) : A.directedDistance x x = 0 :=
  A.rescaledDistanceAt_self x _ _

theorem directedDistance_comm (A : XBallTheoryModel.{u})
    (x y : A.DirectedPoint) :
    A.directedDistance x y = A.directedDistance y x := by
  let larger := A.commonRadius x y + A.commonRadius y x
  have hxy : A.rescaledDistanceAt x y larger
        ((A.left_le_commonRadius x y).trans
          (le_add_of_nonneg_right (zero_le (A.commonRadius y x))))
        ((A.right_le_commonRadius x y).trans
          (le_add_of_nonneg_right (zero_le (A.commonRadius y x)))) =
      A.directedDistance x y :=
    A.rescaledDistanceAt_eq_of_le x y
      (A.left_le_commonRadius x y) (A.right_le_commonRadius x y)
      (le_add_of_nonneg_right (zero_le (A.commonRadius y x)))
  have hyx : A.rescaledDistanceAt y x larger
        ((A.left_le_commonRadius y x).trans
          (le_add_of_nonneg_left (zero_le (A.commonRadius x y))))
        ((A.right_le_commonRadius y x).trans
          (le_add_of_nonneg_left (zero_le (A.commonRadius x y)))) =
      A.directedDistance y x :=
    A.rescaledDistanceAt_eq_of_le y x
      (A.left_le_commonRadius y x) (A.right_le_commonRadius y x)
      (le_add_of_nonneg_left (zero_le (A.commonRadius x y)))
  rw [← hxy, ← hyx]
  unfold rescaledDistanceAt
  rw [dist_comm]

/-- The canonical directed-union distance satisfies the triangle inequality.
All three pairwise distances are first moved to one common enlarged radius,
where the ambient sort's pseudometric triangle inequality applies with one
common normalization factor. -/
theorem directedDistance_triangle (A : XBallTheoryModel.{u})
    (x y z : A.DirectedPoint) :
    A.directedDistance x z ≤
      A.directedDistance x y + A.directedDistance y z := by
  let cxy := A.commonRadius x y
  let cxz := A.commonRadius x z
  let cyz := A.commonRadius y z
  let larger := cxy + (cxz + cyz)
  have hxyLarge : cxy ≤ larger := by
    exact le_add_of_nonneg_right (zero_le (cxz + cyz))
  have hxzLarge : cxz ≤ larger := by
    exact (le_add_of_nonneg_right (zero_le cyz)).trans
      (le_add_of_nonneg_left (zero_le cxy))
  have hyzLarge : cyz ≤ larger := by
    exact (le_add_of_nonneg_left (zero_le cxz)).trans
      (le_add_of_nonneg_left (zero_le cxy))
  have hxy : A.rescaledDistanceAt x y larger
        ((A.left_le_commonRadius x y).trans hxyLarge)
        ((A.right_le_commonRadius x y).trans hxyLarge) =
      A.directedDistance x y :=
    A.rescaledDistanceAt_eq_of_le x y
      (A.left_le_commonRadius x y) (A.right_le_commonRadius x y) hxyLarge
  have hxz : A.rescaledDistanceAt x z larger
        ((A.left_le_commonRadius x z).trans hxzLarge)
        ((A.right_le_commonRadius x z).trans hxzLarge) =
      A.directedDistance x z :=
    A.rescaledDistanceAt_eq_of_le x z
      (A.left_le_commonRadius x z) (A.right_le_commonRadius x z) hxzLarge
  have hyz : A.rescaledDistanceAt y z larger
        ((A.left_le_commonRadius y z).trans hyzLarge)
        ((A.right_le_commonRadius y z).trans hyzLarge) =
      A.directedDistance y z :=
    A.rescaledDistanceAt_eq_of_le y z
      (A.left_le_commonRadius y z) (A.right_le_commonRadius y z) hyzLarge
  rw [← hxz, ← hxy, ← hyz]
  unfold rescaledDistanceAt
  let X := A.model.inclusion
    ((A.left_le_commonRadius x y).trans hxyLarge) x.2
  let Y := A.model.inclusion
    ((A.right_le_commonRadius x y).trans hxyLarge) y.2
  let Z := A.model.inclusion
    ((A.right_le_commonRadius x z).trans hxzLarge) z.2
  change rationalBallMetricBound larger * (dist X Z / A.model.sortBound larger) ≤
    rationalBallMetricBound larger * (dist X Y / A.model.sortBound larger) +
      rationalBallMetricBound larger * (dist Y Z / A.model.sortBound larger)
  have htriangle : dist X Z ≤ dist X Y + dist Y Z :=
    dist_triangle X Y Z
  calc
    rationalBallMetricBound larger * (dist X Z / A.model.sortBound larger) ≤
        rationalBallMetricBound larger *
          ((dist X Y + dist Y Z) / A.model.sortBound larger) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right htriangle
          (A.model.sortBound_pos larger).le)
        (rationalBallMetricBound_pos larger).le
    _ = rationalBallMetricBound larger *
          (dist X Y / A.model.sortBound larger) +
        rationalBallMetricBound larger *
          (dist Y Z / A.model.sortBound larger) := by ring

/-- The raw directed union carries the canonical pseudometric assembled from
the normalization-correct distances on its rational-radius sorts. -/
@[reducible] noncomputable def directedPointPseudoMetricSpace (A : XBallTheoryModel.{u}) :
    PseudoMetricSpace A.DirectedPoint where
  dist := A.directedDistance
  dist_self := A.directedDistance_self
  dist_comm := A.directedDistance_comm
  dist_triangle := A.directedDistance_triangle

noncomputable instance (A : XBallTheoryModel.{u}) :
    PseudoMetricSpace A.DirectedPoint :=
  A.directedPointPseudoMetricSpace

/-- The metric separation of the raw rational-radius directed union. -/
abbrev SeparatedDirectedPoint (A : XBallTheoryModel.{u}) :=
  SeparationQuotient A.DirectedPoint

/-- The canonical map from a radius-tagged point to the separated union. -/
def toSeparatedDirectedPoint (A : XBallTheoryModel.{u}) :
    A.DirectedPoint → A.SeparatedDirectedPoint :=
  SeparationQuotient.mk

/-- Metric separation retains exactly the canonical directed-union
pseudodistance. -/
@[simp] theorem dist_toSeparatedDirectedPoint (A : XBallTheoryModel.{u})
    (x y : A.DirectedPoint) :
    dist (A.toSeparatedDirectedPoint x) (A.toSeparatedDirectedPoint y) =
      A.directedDistance x y :=
  SeparationQuotient.dist_mk x y

/-- Two raw directed-union points have the same image precisely when their
canonical pseudodistance vanishes. -/
theorem toSeparatedDirectedPoint_eq_iff (A : XBallTheoryModel.{u})
    (x y : A.DirectedPoint) :
    A.toSeparatedDirectedPoint x = A.toSeparatedDirectedPoint y ↔
      A.directedDistance x y = 0 := by
  rw [← A.dist_toSeparatedDirectedPoint x y, dist_eq_zero]

/-- Zero distance inside one radius sort implies zero directed distance for
the two corresponding tagged points. -/
theorem directedDistance_sameRadius_eq_zero (A : XBallTheoryModel.{u})
    (r : ℚ≥0) (x y : A.model.Ball r) (hxy : dist x y = 0) :
    A.directedDistance ⟨r, x⟩ ⟨r, y⟩ = 0 := by
  let h : r ≤ r + r := le_add_of_nonneg_right (zero_le r)
  have hincluded :
      dist (A.model.inclusion h x) (A.model.inclusion h y) = 0 := by
    exact Inseparable.dist_eq_zero
      ((Metric.inseparable_iff.mpr hxy).map
        (A.model.inclusion_uniformContinuous h).continuous)
  unfold directedDistance rescaledDistanceAt commonRadius
  apply mul_eq_zero_of_right
  apply (div_eq_zero_iff).2
  left
  convert hincluded

/-- For two representatives in one radius sort, the directed-union distance
is exactly that sort's normalization-corrected distance. -/
theorem directedDistance_sameRadius (A : XBallTheoryModel.{u})
    (r : ℚ≥0) (x y : A.model.Ball r) :
    A.directedDistance ⟨r, x⟩ ⟨r, y⟩ =
      rationalBallMetricBound r * (dist x y / A.model.sortBound r) := by
  let h : r ≤ r + r := le_add_of_nonneg_right (zero_le r)
  calc
    A.directedDistance ⟨r, x⟩ ⟨r, y⟩ =
        A.rescaledDistanceAt ⟨r, x⟩ ⟨r, y⟩ (r + r) h h := by
      rfl
    _ = A.rescaledDistanceAt ⟨r, x⟩ ⟨r, y⟩ r le_rfl le_rfl :=
      A.rescaledDistanceAt_eq_of_le ⟨r, x⟩ ⟨r, y⟩
        le_rfl le_rfl h
    _ = rationalBallMetricBound r *
        (dist x y / A.model.sortBound r) :=
      inclusion_preserves_rescaledDistance_of_sameCompleteTheory
        A.model A.sameCompleteTheory le_rfl x y

/-- A point and its image in any larger radius sort represent the same
element of the directed union. -/
theorem directedDistance_inclusion_representation
    (A : XBallTheoryModel.{u}) {r s : ℚ≥0} (h : r ≤ s)
    (x : A.model.Ball r) :
    A.directedDistance ⟨s, A.model.inclusion h x⟩ ⟨r, x⟩ = 0 := by
  let hs : s ≤ s + r := le_add_of_nonneg_right (zero_le r)
  let hr : r ≤ s + r := le_add_of_nonneg_left (zero_le s)
  have hcomposition :
      dist (A.model.inclusion hs (A.model.inclusion h x))
        (A.model.inclusion (h.trans hs) x) = 0 :=
    dist_inclusion_trans_eq_zero_of_sameCompleteTheory
      A.model A.sameCompleteTheory h hs x
  unfold directedDistance rescaledDistanceAt commonRadius
  apply mul_eq_zero_of_right
  apply (div_eq_zero_iff).2
  left
  convert hcomposition

/-- Radius inclusion is literal equality after metric separation. -/
theorem toSeparatedDirectedPoint_inclusion
    (A : XBallTheoryModel.{u}) {r s : ℚ≥0} (h : r ≤ s)
    (x : A.model.Ball r) :
    A.toSeparatedDirectedPoint ⟨s, A.model.inclusion h x⟩ =
      A.toSeparatedDirectedPoint ⟨r, x⟩ := by
  rw [A.toSeparatedDirectedPoint_eq_iff]
  exact A.directedDistance_inclusion_representation h x

/-! ## The auxiliary Hilbert value on the directed union -/

/-- The unnormalized auxiliary Hilbert value of a radius-tagged point. -/
def directedHilbertValue (A : XBallTheoryModel.{u}) :
    A.DirectedPoint → ℝ
  | ⟨radius, x⟩ => rationalBallMetricBound radius *
      (A.model.predicate (.hilbert radius) x : ℝ)

theorem directedHilbertValue_nonneg
    (A : XBallTheoryModel.{u}) (x : A.DirectedPoint) :
    0 ≤ A.directedHilbertValue x := by
  rcases x with ⟨radius, x⟩
  exact mul_nonneg (rationalBallMetricBound_pos radius).le
    (A.model.predicate (.hilbert radius) x).2.1

/-- Enlarging a radius tag does not change the unnormalized auxiliary
Hilbert value. -/
theorem directedHilbertValue_inclusion
    (A : XBallTheoryModel.{u}) {r s : ℚ≥0} (h : r ≤ s)
    (x : A.model.Ball r) :
    A.directedHilbertValue ⟨s, A.model.inclusion h x⟩ =
      A.directedHilbertValue ⟨r, x⟩ := by
  exact inclusion_preserves_rescaledHilbertNorm_of_sameCompleteTheory
    A.model A.sameCompleteTheory h x

/-- Zero canonical directed pseudodistance forces equality of the auxiliary
Hilbert values. -/
theorem directedHilbertValue_eq_of_directedDistance_eq_zero
    (A : XBallTheoryModel.{u}) (x y : A.DirectedPoint)
    (hxy : A.directedDistance x y = 0) :
    A.directedHilbertValue x = A.directedHilbertValue y := by
  let target := A.commonRadius x y
  let hx : x.1 ≤ target := A.left_le_commonRadius x y
  let hy : y.1 ≤ target := A.right_le_commonRadius x y
  have hxyTarget :
      dist (A.model.inclusion hx x.2) (A.model.inclusion hy y.2) = 0 := by
    unfold directedDistance rescaledDistanceAt at hxy
    exact (div_eq_zero_iff.mp
      ((mul_eq_zero.mp hxy).resolve_left
        (ne_of_gt (rationalBallMetricBound_pos target)))).resolve_right
          (ne_of_gt (A.model.sortBound_pos target))
  have hpredicateTarget :
      A.model.predicate (.hilbert target) (A.model.inclusion hx x.2) =
        A.model.predicate (.hilbert target) (A.model.inclusion hy y.2) := by
    apply dist_eq_zero.mp
    exact Inseparable.dist_eq_zero
      ((Metric.inseparable_iff.mpr hxyTarget).map
        (A.model.predicate_uniformContinuous (.hilbert target)).continuous)
  calc
    A.directedHilbertValue x =
        rationalBallMetricBound target *
          (A.model.predicate (.hilbert target)
            (A.model.inclusion hx x.2) : ℝ) :=
      (inclusion_preserves_rescaledHilbertNorm_of_sameCompleteTheory
        A.model A.sameCompleteTheory hx x.2).symm
    _ = rationalBallMetricBound target *
          (A.model.predicate (.hilbert target)
            (A.model.inclusion hy y.2) : ℝ) := by
      rw [hpredicateTarget]
    _ = A.directedHilbertValue y :=
      inclusion_preserves_rescaledHilbertNorm_of_sameCompleteTheory
        A.model A.sameCompleteTheory hy y.2

/-- The auxiliary Hilbert value descended through metric separation. -/
def separatedHilbertValue (A : XBallTheoryModel.{u}) :
    A.SeparatedDirectedPoint → ℝ :=
  Quotient.lift A.directedHilbertValue fun x y hxy =>
    A.directedHilbertValue_eq_of_directedDistance_eq_zero x y
      (Metric.inseparable_iff.mp hxy)

/-- The descended auxiliary Hilbert value has the expected representative
formula. -/
@[simp] theorem separatedHilbertValue_toSeparatedDirectedPoint
    (A : XBallTheoryModel.{u}) (x : A.DirectedPoint) :
    A.separatedHilbertValue (A.toSeparatedDirectedPoint x) =
      A.directedHilbertValue x :=
  rfl

theorem separatedHilbertValue_nonneg
    (A : XBallTheoryModel.{u}) (x : A.SeparatedDirectedPoint) :
    0 ≤ A.separatedHilbertValue x := by
  refine Quotient.inductionOn' x ?_
  exact A.directedHilbertValue_nonneg

/-- The auxiliary Hilbert value is sharply controlled by the canonical
directed distance. -/
theorem abs_directedHilbertValue_sub_le_directedDistance
    (A : XBallTheoryModel.{u}) (x y : A.DirectedPoint) :
    |A.directedHilbertValue x - A.directedHilbertValue y| ≤
      A.directedDistance x y := by
  let target := A.commonRadius x y
  let hx : x.1 ≤ target := A.left_le_commonRadius x y
  let hy : y.1 ≤ target := A.right_le_commonRadius x y
  have hxValue :=
    inclusion_preserves_rescaledHilbertNorm_of_sameCompleteTheory
      A.model A.sameCompleteTheory hx x.2
  have hyValue :=
    inclusion_preserves_rescaledHilbertNorm_of_sameCompleteTheory
      A.model A.sameCompleteTheory hy y.2
  have htarget :=
    hilbertNorm_rescaledDistance_le_of_sameCompleteTheory
      A.model A.sameCompleteTheory target
      (A.model.inclusion hx x.2) (A.model.inclusion hy y.2)
  change |rationalBallMetricBound x.1 *
      (A.model.predicate (.hilbert x.1) x.2 : ℝ) -
    rationalBallMetricBound y.1 *
      (A.model.predicate (.hilbert y.1) y.2 : ℝ)| ≤
    A.directedDistance x y
  rw [← hxValue, ← hyValue]
  change _ ≤ A.rescaledDistanceAt x y target hx hy
  exact htarget

/-- The descended auxiliary Hilbert value is `1`-Lipschitz for the separated
directed-union metric. -/
theorem abs_separatedHilbertValue_sub_le_dist
    (A : XBallTheoryModel.{u}) (x y : A.SeparatedDirectedPoint) :
    |A.separatedHilbertValue x - A.separatedHilbertValue y| ≤ dist x y := by
  refine Quotient.inductionOn' x ?_
  intro x
  refine Quotient.inductionOn' y ?_
  intro y
  change |A.directedHilbertValue x - A.directedHilbertValue y| ≤
    dist (A.toSeparatedDirectedPoint x) (A.toSeparatedDirectedPoint y)
  rw [A.dist_toSeparatedDirectedPoint]
  exact A.abs_directedHilbertValue_sub_le_directedDistance x y

theorem separatedHilbertValue_lipschitzWith
    (A : XBallTheoryModel.{u}) :
    LipschitzWith 1 A.separatedHilbertValue := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [Real.dist_eq] using
    A.abs_separatedHilbertValue_sub_le_dist x y

theorem separatedHilbertValue_uniformContinuous
    (A : XBallTheoryModel.{u}) :
    UniformContinuous A.separatedHilbertValue :=
  A.separatedHilbertValue_lipschitzWith.uniformContinuous

/-- A distinguished zero representative, chosen in the radius-zero sort. -/
def directedZero (A : XBallTheoryModel.{u}) : A.DirectedPoint :=
  ⟨0, A.model.zero 0⟩

/-- Every sort's named zero represents the distinguished directed zero. -/
theorem directedDistance_zero_representation (A : XBallTheoryModel.{u})
    (r : ℚ≥0) :
    A.directedDistance A.directedZero ⟨r, A.model.zero r⟩ = 0 := by
  unfold directedDistance rescaledDistanceAt commonRadius directedZero
  simp only [zero_add]
  have hzero := dist_inclusion_zero_eq_zero_of_sameCompleteTheory
    A.model A.sameCompleteTheory (zero_le r)
  have hrefl := dist_inclusion_refl_eq_zero_of_sameCompleteTheory
    A.model A.sameCompleteTheory r (A.model.zero r)
  have hdist :
      dist (A.model.inclusion (zero_le r) (A.model.zero 0))
        (A.model.inclusion (le_refl r) (A.model.zero r)) = 0 := by
    calc
      dist (A.model.inclusion (zero_le r) (A.model.zero 0))
          (A.model.inclusion (le_refl r) (A.model.zero r)) =
        dist (A.model.zero r)
          (A.model.inclusion (le_refl r) (A.model.zero r)) := by
            rw [dist_comm]
            rw [PseudoMetricSpace.dist_eq_of_dist_zero _ hzero]
            rw [dist_comm]
      _ = dist (A.model.zero r) (A.model.zero r) :=
        PseudoMetricSpace.dist_eq_of_dist_zero _ hrefl
      _ = 0 := dist_self _
  apply mul_eq_zero_of_right
  apply (div_eq_zero_iff).2
  left
  convert hdist <;> simp

/-- Negate a radius-tagged point without changing its radius tag. -/
def directedNeg (A : XBallTheoryModel.{u}) :
    A.DirectedPoint → A.DirectedPoint
  | ⟨r, x⟩ => ⟨r, A.model.neg r x⟩

/-- Negation preserves zero directed pseudodistance. This is the precise
representative-independence statement needed to descend negation through
metric separation. -/
theorem directedDistance_neg_eq_zero_of_eq_zero
    (A : XBallTheoryModel.{u}) (x y : A.DirectedPoint)
    (hxy : A.directedDistance x y = 0) :
    A.directedDistance (A.directedNeg x) (A.directedNeg y) = 0 := by
  let target := A.commonRadius x y
  let hx : x.1 ≤ target := A.left_le_commonRadius x y
  let hy : y.1 ≤ target := A.right_le_commonRadius x y
  have hxyTarget :
      dist (A.model.inclusion hx x.2) (A.model.inclusion hy y.2) = 0 := by
    unfold directedDistance rescaledDistanceAt at hxy
    exact (div_eq_zero_iff.mp
      ((mul_eq_zero.mp hxy).resolve_left
        (ne_of_gt (rationalBallMetricBound_pos target)))).resolve_right
          (ne_of_gt (A.model.sortBound_pos target))
  have hnegTarget :
      dist (A.model.neg target (A.model.inclusion hx x.2))
        (A.model.neg target (A.model.inclusion hy y.2)) = 0 := by
    exact Inseparable.dist_eq_zero
      ((Metric.inseparable_iff.mpr hxyTarget).map
        (A.model.neg_uniformContinuous target).continuous)
  have hxNeg :
      dist (A.model.inclusion hx (A.model.neg x.1 x.2))
        (A.model.neg target (A.model.inclusion hx x.2)) = 0 :=
    dist_inclusion_neg_eq_zero_of_sameCompleteTheory
      A.model A.sameCompleteTheory hx x.2
  have hyNeg :
      dist (A.model.inclusion hy (A.model.neg y.1 y.2))
        (A.model.neg target (A.model.inclusion hy y.2)) = 0 :=
    dist_inclusion_neg_eq_zero_of_sameCompleteTheory
      A.model A.sameCompleteTheory hy y.2
  unfold directedDistance rescaledDistanceAt directedNeg
  change rationalBallMetricBound target *
      (dist (A.model.inclusion hx (A.model.neg x.1 x.2))
        (A.model.inclusion hy (A.model.neg y.1 y.2)) /
          A.model.sortBound target) = 0
  have hdist :
      dist (A.model.inclusion hx (A.model.neg x.1 x.2))
        (A.model.inclusion hy (A.model.neg y.1 y.2)) = 0 := by
    calc
      dist (A.model.inclusion hx (A.model.neg x.1 x.2))
          (A.model.inclusion hy (A.model.neg y.1 y.2)) =
        dist (A.model.neg target (A.model.inclusion hx x.2))
          (A.model.inclusion hy (A.model.neg y.1 y.2)) := by
            rw [dist_comm]
            rw [PseudoMetricSpace.dist_eq_of_dist_zero _ hxNeg]
            rw [dist_comm]
      _ = dist (A.model.neg target (A.model.inclusion hx x.2))
          (A.model.neg target (A.model.inclusion hy y.2)) :=
        PseudoMetricSpace.dist_eq_of_dist_zero _ hyNeg
      _ = 0 := hnegTarget
  rw [hdist]
  simp

/-- Double raw negation has zero directed distance from the original tagged
point, by transfer of the universal involutive-negation sentence. -/
theorem directedDistance_neg_neg_eq_zero
    (A : XBallTheoryModel.{u}) (x : A.DirectedPoint) :
    A.directedDistance (A.directedNeg (A.directedNeg x)) x = 0 := by
  rcases x with ⟨r, x⟩
  exact A.directedDistance_sameRadius_eq_zero r
    (A.model.neg r (A.model.neg r x)) x
    (dist_neg_neg_eq_zero_of_sameCompleteTheory
      A.model A.sameCompleteTheory r x)

/-- Add two radius-tagged points; the output carries the sum radius. -/
def directedAdd (A : XBallTheoryModel.{u}) :
    A.DirectedPoint → A.DirectedPoint → A.DirectedPoint
  | ⟨r, x⟩, ⟨s, y⟩ => ⟨r + s, A.model.add r s (x, y)⟩

/-- Binary addition preserves zero directed pseudodistance in both
arguments. Both pairs are moved to the common radius of the two sums, and
the resulting additions are compared in twice that radius. -/
theorem directedDistance_add_eq_zero_of_eq_zero
    (A : XBallTheoryModel.{u}) (x x' y y' : A.DirectedPoint)
    (hxx' : A.directedDistance x x' = 0)
    (hyy' : A.directedDistance y y' = 0) :
    A.directedDistance (A.directedAdd x y) (A.directedAdd x' y') = 0 := by
  let leftSum := A.directedAdd x y
  let rightSum := A.directedAdd x' y'
  let target := A.commonRadius leftSum rightSum
  have hx : x.1 ≤ target := by
    exact (le_add_of_nonneg_right (zero_le y.1)).trans
      (A.left_le_commonRadius leftSum rightSum)
  have hy : y.1 ≤ target := by
    exact (le_add_of_nonneg_left (zero_le x.1)).trans
      (A.left_le_commonRadius leftSum rightSum)
  have hx' : x'.1 ≤ target := by
    exact (le_add_of_nonneg_right (zero_le y'.1)).trans
      (A.right_le_commonRadius leftSum rightSum)
  have hy' : y'.1 ≤ target := by
    exact (le_add_of_nonneg_left (zero_le x'.1)).trans
      (A.right_le_commonRadius leftSum rightSum)
  have hxxCommon : A.commonRadius x x' ≤ target :=
    add_le_add
      (le_add_of_nonneg_right (zero_le y.1))
      (le_add_of_nonneg_right (zero_le y'.1))
  have hyyCommon : A.commonRadius y y' ≤ target :=
    add_le_add
      (le_add_of_nonneg_left (zero_le x.1))
      (le_add_of_nonneg_left (zero_le x'.1))
  have hxxAt :
      A.rescaledDistanceAt x x' target
          ((A.left_le_commonRadius x x').trans hxxCommon)
          ((A.right_le_commonRadius x x').trans hxxCommon) = 0 := by
    rw [A.rescaledDistanceAt_eq_of_le x x'
      (A.left_le_commonRadius x x') (A.right_le_commonRadius x x') hxxCommon]
    exact hxx'
  have hyyAt :
      A.rescaledDistanceAt y y' target
          ((A.left_le_commonRadius y y').trans hyyCommon)
          ((A.right_le_commonRadius y y').trans hyyCommon) = 0 := by
    rw [A.rescaledDistanceAt_eq_of_le y y'
      (A.left_le_commonRadius y y') (A.right_le_commonRadius y y') hyyCommon]
    exact hyy'
  have hxxDist :
      dist (A.model.inclusion hx x.2) (A.model.inclusion hx' x'.2) = 0 := by
    unfold rescaledDistanceAt at hxxAt
    have := (div_eq_zero_iff.mp
      ((mul_eq_zero.mp hxxAt).resolve_left
        (ne_of_gt (rationalBallMetricBound_pos target)))).resolve_right
          (ne_of_gt (A.model.sortBound_pos target))
    convert this
  have hyyDist :
      dist (A.model.inclusion hy y.2) (A.model.inclusion hy' y'.2) = 0 := by
    unfold rescaledDistanceAt at hyyAt
    have := (div_eq_zero_iff.mp
      ((mul_eq_zero.mp hyyAt).resolve_left
        (ne_of_gt (rationalBallMetricBound_pos target)))).resolve_right
          (ne_of_gt (A.model.sortBound_pos target))
    convert this
  have haddDist :
      dist
          (A.model.add target target
            (A.model.inclusion hx x.2, A.model.inclusion hy y.2))
          (A.model.add target target
            (A.model.inclusion hx' x'.2, A.model.inclusion hy' y'.2)) = 0 := by
    exact Inseparable.dist_eq_zero
      (((Metric.inseparable_iff.mpr hxxDist).prod
        (Metric.inseparable_iff.mpr hyyDist)).map
          (A.model.add_uniformContinuous target target).continuous)
  have hleft :
      dist
          (A.model.inclusion (add_le_add hx hy)
            (A.model.add x.1 y.1 (x.2, y.2)))
          (A.model.add target target
            (A.model.inclusion hx x.2, A.model.inclusion hy y.2)) = 0 :=
    dist_inclusion_add_eq_zero_of_sameCompleteTheory
      A.model A.sameCompleteTheory hx hy x.2 y.2
  have hright :
      dist
          (A.model.inclusion (add_le_add hx' hy')
            (A.model.add x'.1 y'.1 (x'.2, y'.2)))
          (A.model.add target target
            (A.model.inclusion hx' x'.2, A.model.inclusion hy' y'.2)) = 0 :=
    dist_inclusion_add_eq_zero_of_sameCompleteTheory
      A.model A.sameCompleteTheory hx' hy' x'.2 y'.2
  have hdist :
      dist
          (A.model.inclusion (add_le_add hx hy)
            (A.model.add x.1 y.1 (x.2, y.2)))
          (A.model.inclusion (add_le_add hx' hy')
            (A.model.add x'.1 y'.1 (x'.2, y'.2))) = 0 := by
    calc
      dist (A.model.inclusion (add_le_add hx hy)
            (A.model.add x.1 y.1 (x.2, y.2)))
          (A.model.inclusion (add_le_add hx' hy')
            (A.model.add x'.1 y'.1 (x'.2, y'.2))) =
        dist (A.model.add target target
            (A.model.inclusion hx x.2, A.model.inclusion hy y.2))
          (A.model.inclusion (add_le_add hx' hy')
            (A.model.add x'.1 y'.1 (x'.2, y'.2))) := by
              rw [dist_comm]
              rw [PseudoMetricSpace.dist_eq_of_dist_zero _ hleft]
              rw [dist_comm]
      _ = dist (A.model.add target target
            (A.model.inclusion hx x.2, A.model.inclusion hy y.2))
          (A.model.add target target
            (A.model.inclusion hx' x'.2, A.model.inclusion hy' y'.2)) :=
        PseudoMetricSpace.dist_eq_of_dist_zero _ hright
      _ = 0 := haddDist
  have htarget : A.commonRadius leftSum rightSum ≤ target + target :=
    le_add_of_nonneg_right (zero_le target)
  change A.directedDistance leftSum rightSum = 0
  unfold directedDistance
  rw [← A.rescaledDistanceAt_eq_of_le leftSum rightSum
    (A.left_le_commonRadius leftSum rightSum)
    (A.right_le_commonRadius leftSum rightSum) htarget]
  unfold rescaledDistanceAt leftSum rightSum directedAdd
  apply mul_eq_zero_of_right
  apply (div_eq_zero_iff).2
  left
  convert hdist

/-- Multiply a radius-tagged point by a rational scalar, recording the exact
output radius. -/
def directedSmul (A : XBallTheoryModel.{u}) (q : ℚ) :
    A.DirectedPoint → A.DirectedPoint
  | ⟨r, x⟩ => ⟨q.nnabs * r, A.model.smul q r x⟩

/-- The unnormalized auxiliary Hilbert value is exactly homogeneous under
rational scalar multiplication on tagged directed points. -/
theorem directedHilbertValue_smul
    (A : XBallTheoryModel.{u}) (q : ℚ) (x : A.DirectedPoint) :
    A.directedHilbertValue (A.directedSmul q x) =
      (q.nnabs : ℝ) * A.directedHilbertValue x := by
  rcases x with ⟨r, x⟩
  simpa [directedHilbertValue, directedSmul, mul_assoc] using
    (smul_preserves_rescaledHilbertNorm_of_sameCompleteTheory
      A.model A.sameCompleteTheory q r x)

/-- Rational scalar multiplication preserves zero directed
pseudodistance and therefore is independent of the chosen representative. -/
theorem directedDistance_smul_eq_zero_of_eq_zero
    (A : XBallTheoryModel.{u}) (q : ℚ) (x y : A.DirectedPoint)
    (hxy : A.directedDistance x y = 0) :
    A.directedDistance (A.directedSmul q x) (A.directedSmul q y) = 0 := by
  let target := A.commonRadius x y
  let hx : x.1 ≤ target := A.left_le_commonRadius x y
  let hy : y.1 ≤ target := A.right_le_commonRadius x y
  have hxyTarget :
      dist (A.model.inclusion hx x.2) (A.model.inclusion hy y.2) = 0 := by
    unfold directedDistance rescaledDistanceAt at hxy
    exact (div_eq_zero_iff.mp
      ((mul_eq_zero.mp hxy).resolve_left
        (ne_of_gt (rationalBallMetricBound_pos target)))).resolve_right
          (ne_of_gt (A.model.sortBound_pos target))
  have hsmulTarget :
      dist (A.model.smul q target (A.model.inclusion hx x.2))
        (A.model.smul q target (A.model.inclusion hy y.2)) = 0 := by
    exact Inseparable.dist_eq_zero
      ((Metric.inseparable_iff.mpr hxyTarget).map
        (A.model.smul_uniformContinuous q target).continuous)
  have hxSmul :
      dist
          (A.model.inclusion (nnabs_mul_mono hx q)
            (A.model.smul q x.1 x.2))
          (A.model.smul q target (A.model.inclusion hx x.2)) = 0 :=
    dist_inclusion_smul_eq_zero_of_sameCompleteTheory
      A.model A.sameCompleteTheory hx q x.2
  have hySmul :
      dist
          (A.model.inclusion (nnabs_mul_mono hy q)
            (A.model.smul q y.1 y.2))
          (A.model.smul q target (A.model.inclusion hy y.2)) = 0 :=
    dist_inclusion_smul_eq_zero_of_sameCompleteTheory
      A.model A.sameCompleteTheory hy q y.2
  have hdist :
      dist
          (A.model.inclusion (nnabs_mul_mono hx q)
            (A.model.smul q x.1 x.2))
          (A.model.inclusion (nnabs_mul_mono hy q)
            (A.model.smul q y.1 y.2)) = 0 := by
    calc
      dist (A.model.inclusion (nnabs_mul_mono hx q)
            (A.model.smul q x.1 x.2))
          (A.model.inclusion (nnabs_mul_mono hy q)
            (A.model.smul q y.1 y.2)) =
        dist (A.model.smul q target (A.model.inclusion hx x.2))
          (A.model.inclusion (nnabs_mul_mono hy q)
            (A.model.smul q y.1 y.2)) := by
              rw [dist_comm]
              rw [PseudoMetricSpace.dist_eq_of_dist_zero _ hxSmul]
              rw [dist_comm]
      _ = dist (A.model.smul q target (A.model.inclusion hx x.2))
          (A.model.smul q target (A.model.inclusion hy y.2)) :=
        PseudoMetricSpace.dist_eq_of_dist_zero _ hySmul
      _ = 0 := hsmulTarget
  have hradius :
      A.commonRadius (A.directedSmul q x) (A.directedSmul q y) =
        q.nnabs * target := by
    rcases x with ⟨r, x⟩
    rcases y with ⟨s, y⟩
    simp [directedSmul, commonRadius, target, mul_add]
  have hscaled :
      A.rescaledDistanceAt (A.directedSmul q x) (A.directedSmul q y)
          (q.nnabs * target) (nnabs_mul_mono hx q) (nnabs_mul_mono hy q) = 0 := by
    unfold rescaledDistanceAt
    apply mul_eq_zero_of_right
    apply (div_eq_zero_iff).2
    left
    convert hdist
  calc
    A.directedDistance (A.directedSmul q x) (A.directedSmul q y) =
        A.rescaledDistanceAt (A.directedSmul q x) (A.directedSmul q y)
          (q.nnabs * target) (nnabs_mul_mono hx q) (nnabs_mul_mono hy q) := by
            unfold directedDistance
            congr 1
    _ = 0 := hscaled

/-- The distinguished zero of the separated directed union. -/
def separatedZero (A : XBallTheoryModel.{u}) : A.SeparatedDirectedPoint :=
  A.toSeparatedDirectedPoint A.directedZero

/-- Negation descended to the metric-separated directed union. -/
def separatedNeg (A : XBallTheoryModel.{u}) :
    A.SeparatedDirectedPoint → A.SeparatedDirectedPoint :=
  Quotient.map' A.directedNeg fun x y hxy =>
    Metric.inseparable_iff.mpr
      (A.directedDistance_neg_eq_zero_of_eq_zero x y
        (Metric.inseparable_iff.mp hxy))

/-- Addition descended to the metric-separated directed union. -/
def separatedAdd (A : XBallTheoryModel.{u}) :
    A.SeparatedDirectedPoint → A.SeparatedDirectedPoint →
      A.SeparatedDirectedPoint :=
  Quotient.map₂ A.directedAdd fun x x' hxx' y y' hyy' =>
    Metric.inseparable_iff.mpr
      (A.directedDistance_add_eq_zero_of_eq_zero x x' y y'
        (Metric.inseparable_iff.mp hxx')
        (Metric.inseparable_iff.mp hyy'))

/-- Rational scalar multiplication descended to the metric-separated
directed union. -/
def separatedSmul (A : XBallTheoryModel.{u}) (q : ℚ) :
    A.SeparatedDirectedPoint → A.SeparatedDirectedPoint :=
  Quotient.map' (A.directedSmul q) fun x y hxy =>
    Metric.inseparable_iff.mpr
      (A.directedDistance_smul_eq_zero_of_eq_zero q x y
        (Metric.inseparable_iff.mp hxy))

@[simp] theorem separatedNeg_toSeparatedDirectedPoint
    (A : XBallTheoryModel.{u}) (x : A.DirectedPoint) :
    A.separatedNeg (A.toSeparatedDirectedPoint x) =
      A.toSeparatedDirectedPoint (A.directedNeg x) :=
  rfl

/-- Negation is literally involutive after metric separation. -/
@[simp] theorem separatedNeg_neg (A : XBallTheoryModel.{u})
    (x : A.SeparatedDirectedPoint) :
    A.separatedNeg (A.separatedNeg x) = x := by
  refine Quotient.inductionOn' x ?_
  intro representative
  change A.separatedNeg
      (A.separatedNeg (A.toSeparatedDirectedPoint representative)) =
    A.toSeparatedDirectedPoint representative
  rw [A.separatedNeg_toSeparatedDirectedPoint,
    A.separatedNeg_toSeparatedDirectedPoint]
  rw [A.toSeparatedDirectedPoint_eq_iff]
  exact A.directedDistance_neg_neg_eq_zero representative

/-- The zero named in any radius sort maps to the separated zero. -/
theorem toSeparatedDirectedPoint_zero (A : XBallTheoryModel.{u})
    (r : ℚ≥0) :
    A.toSeparatedDirectedPoint ⟨r, A.model.zero r⟩ = A.separatedZero := by
  unfold separatedZero
  rw [A.toSeparatedDirectedPoint_eq_iff]
  rw [A.directedDistance_comm]
  exact A.directedDistance_zero_representation r

/-- The auxiliary Hilbert value is bounded above by distance from zero on
the metric-separated directed union.  This is the unnormalized form of the
first comparison sentence transferred from the distinguished expansion. -/
theorem separatedHilbertValue_le_dist_zero
    (A : XBallTheoryModel.{u}) (x : A.SeparatedDirectedPoint) :
    A.separatedHilbertValue x ≤ dist x A.separatedZero := by
  refine Quotient.inductionOn' x ?_
  rintro ⟨r, x⟩
  have hcomparison := comparisons_of_sameCompleteTheory
    A.model A.sameCompleteTheory r x
  change
    (A.model.predicate (.hilbert r) x : ℝ) ≤
        dist x (A.model.zero r) / A.model.sortBound r ∧
      dist x (A.model.zero r) / A.model.sortBound r ≤
        Real.sqrt 3 * (A.model.predicate (.hilbert r) x : ℝ)
    at hcomparison
  change rationalBallMetricBound r *
      (A.model.predicate (.hilbert r) x : ℝ) ≤
    dist (A.toSeparatedDirectedPoint ⟨r, x⟩) A.separatedZero
  rw [← A.toSeparatedDirectedPoint_zero r,
    A.dist_toSeparatedDirectedPoint, A.directedDistance_sameRadius]
  exact mul_le_mul_of_nonneg_left hcomparison.1
    (rationalBallMetricBound_pos r).le

/-- Distance from zero is bounded by `sqrt 3` times the auxiliary Hilbert
value on the metric-separated directed union.  This is the unnormalized
form of the second transferred comparison sentence. -/
theorem dist_zero_le_sqrtThree_mul_separatedHilbertValue
    (A : XBallTheoryModel.{u}) (x : A.SeparatedDirectedPoint) :
    dist x A.separatedZero ≤
      Real.sqrt 3 * A.separatedHilbertValue x := by
  refine Quotient.inductionOn' x ?_
  rintro ⟨r, x⟩
  have hcomparison := comparisons_of_sameCompleteTheory
    A.model A.sameCompleteTheory r x
  change
    (A.model.predicate (.hilbert r) x : ℝ) ≤
        dist x (A.model.zero r) / A.model.sortBound r ∧
      dist x (A.model.zero r) / A.model.sortBound r ≤
        Real.sqrt 3 * (A.model.predicate (.hilbert r) x : ℝ)
    at hcomparison
  change
    dist (A.toSeparatedDirectedPoint ⟨r, x⟩) A.separatedZero ≤
      Real.sqrt 3 * (rationalBallMetricBound r *
        (A.model.predicate (.hilbert r) x : ℝ))
  rw [← A.toSeparatedDirectedPoint_zero r,
    A.dist_toSeparatedDirectedPoint, A.directedDistance_sameRadius]
  calc
    rationalBallMetricBound r *
          (dist x (A.model.zero r) / A.model.sortBound r) ≤
        rationalBallMetricBound r *
          (Real.sqrt 3 * (A.model.predicate (.hilbert r) x : ℝ)) :=
      mul_le_mul_of_nonneg_left hcomparison.2
        (rationalBallMetricBound_pos r).le
    _ = Real.sqrt 3 * (rationalBallMetricBound r *
          (A.model.predicate (.hilbert r) x : ℝ)) := by ring

@[simp] theorem separatedAdd_toSeparatedDirectedPoint
    (A : XBallTheoryModel.{u}) (x y : A.DirectedPoint) :
    A.separatedAdd (A.toSeparatedDirectedPoint x)
        (A.toSeparatedDirectedPoint y) =
      A.toSeparatedDirectedPoint (A.directedAdd x y) :=
  rfl

/-- Right translation preserves distance when the two translated points are
represented in one common source radius. -/
theorem dist_separatedAdd_right_sameRadius (A : XBallTheoryModel.{u})
    (r s : ℚ≥0) (x y : A.model.Ball r) (z : A.model.Ball s) :
    dist
        (A.separatedAdd (A.toSeparatedDirectedPoint ⟨r, x⟩)
          (A.toSeparatedDirectedPoint ⟨s, z⟩))
        (A.separatedAdd (A.toSeparatedDirectedPoint ⟨r, y⟩)
          (A.toSeparatedDirectedPoint ⟨s, z⟩)) =
      dist (A.toSeparatedDirectedPoint ⟨r, x⟩)
        (A.toSeparatedDirectedPoint ⟨r, y⟩) := by
  rw [A.separatedAdd_toSeparatedDirectedPoint,
    A.separatedAdd_toSeparatedDirectedPoint,
    A.dist_toSeparatedDirectedPoint,
    A.dist_toSeparatedDirectedPoint]
  change A.directedDistance
      ⟨r + s, A.model.add r s (x, z)⟩
      ⟨r + s, A.model.add r s (y, z)⟩ =
    A.directedDistance ⟨r, x⟩ ⟨r, y⟩
  rw [A.directedDistance_sameRadius, A.directedDistance_sameRadius]
  exact addition_preserves_rescaledDistance_right_of_sameCompleteTheory
    A.model A.sameCompleteTheory r s x y z

/-- Right translation is an isometry of the entire separated directed union.
Representatives of the two varying points are first included into one common
radius, where the transferred typed metric law applies. -/
theorem dist_separatedAdd_right (A : XBallTheoryModel.{u})
    (x y z : A.SeparatedDirectedPoint) :
    dist (A.separatedAdd x z) (A.separatedAdd y z) = dist x y := by
  refine Quotient.inductionOn' x ?_
  intro xRepresentative
  refine Quotient.inductionOn' y ?_
  intro yRepresentative
  refine Quotient.inductionOn' z ?_
  intro zRepresentative
  rcases xRepresentative with ⟨r, x⟩
  rcases yRepresentative with ⟨t, y⟩
  rcases zRepresentative with ⟨s, z⟩
  let target := r + t
  let hx : r ≤ target := le_add_of_nonneg_right (zero_le t)
  let hy : t ≤ target := le_add_of_nonneg_left (zero_le r)
  change dist
      (A.separatedAdd (A.toSeparatedDirectedPoint ⟨r, x⟩)
        (A.toSeparatedDirectedPoint ⟨s, z⟩))
      (A.separatedAdd (A.toSeparatedDirectedPoint ⟨t, y⟩)
        (A.toSeparatedDirectedPoint ⟨s, z⟩)) =
    dist (A.toSeparatedDirectedPoint ⟨r, x⟩)
      (A.toSeparatedDirectedPoint ⟨t, y⟩)
  rw [← A.toSeparatedDirectedPoint_inclusion hx x,
    ← A.toSeparatedDirectedPoint_inclusion hy y]
  exact A.dist_separatedAdd_right_sameRadius target s
    (A.model.inclusion hx x) (A.model.inclusion hy y) z

/-- Addition by a fixed element on the right is an isometry. -/
theorem separatedAdd_right_isometry (A : XBallTheoryModel.{u})
    (z : A.SeparatedDirectedPoint) :
    Isometry (fun x ↦ A.separatedAdd x z) :=
  Isometry.of_dist_eq fun x y ↦ A.dist_separatedAdd_right x y z

theorem separatedAdd_right_uniformContinuous (A : XBallTheoryModel.{u})
    (z : A.SeparatedDirectedPoint) :
    UniformContinuous (fun x ↦ A.separatedAdd x z) :=
  (A.separatedAdd_right_isometry z).uniformContinuous

/-- The separated zero is a right identity for descended addition. -/
theorem separatedAdd_zero (A : XBallTheoryModel.{u})
    (x : A.SeparatedDirectedPoint) :
    A.separatedAdd x A.separatedZero = x := by
  refine Quotient.inductionOn' x ?_
  rintro ⟨r, x⟩
  change A.separatedAdd (A.toSeparatedDirectedPoint ⟨r, x⟩)
      A.separatedZero = A.toSeparatedDirectedPoint ⟨r, x⟩
  rw [← A.toSeparatedDirectedPoint_zero r]
  rw [A.separatedAdd_toSeparatedDirectedPoint]
  let h : r ≤ r + r := le_add_of_nonneg_right (zero_le r)
  calc
    A.toSeparatedDirectedPoint
        (A.directedAdd ⟨r, x⟩ ⟨r, A.model.zero r⟩) =
      A.toSeparatedDirectedPoint ⟨r + r, A.model.inclusion h x⟩ := by
        rw [A.toSeparatedDirectedPoint_eq_iff]
        apply A.directedDistance_sameRadius_eq_zero
        exact dist_add_zero_eq_zero_of_sameCompleteTheory
          A.model A.sameCompleteTheory r x
    _ = A.toSeparatedDirectedPoint ⟨r, x⟩ :=
      A.toSeparatedDirectedPoint_inclusion h x

/-- The separated zero is a left identity for descended addition. -/
theorem separatedZero_add (A : XBallTheoryModel.{u})
    (x : A.SeparatedDirectedPoint) :
    A.separatedAdd A.separatedZero x = x := by
  refine Quotient.inductionOn' x ?_
  rintro ⟨r, x⟩
  change A.separatedAdd A.separatedZero
      (A.toSeparatedDirectedPoint ⟨r, x⟩) =
    A.toSeparatedDirectedPoint ⟨r, x⟩
  rw [← A.toSeparatedDirectedPoint_zero r]
  rw [A.separatedAdd_toSeparatedDirectedPoint]
  let h : r ≤ r + r := le_add_of_nonneg_left (zero_le r)
  calc
    A.toSeparatedDirectedPoint
        (A.directedAdd ⟨r, A.model.zero r⟩ ⟨r, x⟩) =
      A.toSeparatedDirectedPoint ⟨r + r, A.model.inclusion h x⟩ := by
        rw [A.toSeparatedDirectedPoint_eq_iff]
        apply A.directedDistance_sameRadius_eq_zero
        exact dist_zero_add_eq_zero_of_sameCompleteTheory
          A.model A.sameCompleteTheory r x
    _ = A.toSeparatedDirectedPoint ⟨r, x⟩ :=
      A.toSeparatedDirectedPoint_inclusion h x

/-- Every separated element added to its negation is the separated zero. -/
theorem separatedAdd_neg (A : XBallTheoryModel.{u})
    (x : A.SeparatedDirectedPoint) :
    A.separatedAdd x (A.separatedNeg x) = A.separatedZero := by
  refine Quotient.inductionOn' x ?_
  rintro ⟨r, x⟩
  change A.separatedAdd (A.toSeparatedDirectedPoint ⟨r, x⟩)
      (A.separatedNeg (A.toSeparatedDirectedPoint ⟨r, x⟩)) =
    A.separatedZero
  rw [A.separatedNeg_toSeparatedDirectedPoint,
    A.separatedAdd_toSeparatedDirectedPoint]
  calc
    A.toSeparatedDirectedPoint
        (A.directedAdd ⟨r, x⟩ (A.directedNeg ⟨r, x⟩)) =
      A.toSeparatedDirectedPoint ⟨r + r, A.model.zero (r + r)⟩ := by
        rw [A.toSeparatedDirectedPoint_eq_iff]
        apply A.directedDistance_sameRadius_eq_zero
        exact dist_add_neg_eq_zero_of_sameCompleteTheory
          A.model A.sameCompleteTheory r x
    _ = A.separatedZero := A.toSeparatedDirectedPoint_zero (r + r)

/-- The negation of every separated element added to it is the separated
zero. -/
theorem separatedNeg_add (A : XBallTheoryModel.{u})
    (x : A.SeparatedDirectedPoint) :
    A.separatedAdd (A.separatedNeg x) x = A.separatedZero := by
  refine Quotient.inductionOn' x ?_
  rintro ⟨r, x⟩
  change A.separatedAdd
      (A.separatedNeg (A.toSeparatedDirectedPoint ⟨r, x⟩))
      (A.toSeparatedDirectedPoint ⟨r, x⟩) = A.separatedZero
  rw [A.separatedNeg_toSeparatedDirectedPoint,
    A.separatedAdd_toSeparatedDirectedPoint]
  calc
    A.toSeparatedDirectedPoint
        (A.directedAdd (A.directedNeg ⟨r, x⟩) ⟨r, x⟩) =
      A.toSeparatedDirectedPoint ⟨r + r, A.model.zero (r + r)⟩ := by
        rw [A.toSeparatedDirectedPoint_eq_iff]
        apply A.directedDistance_sameRadius_eq_zero
        exact dist_neg_add_eq_zero_of_sameCompleteTheory
          A.model A.sameCompleteTheory r x
    _ = A.separatedZero := A.toSeparatedDirectedPoint_zero (r + r)

/-- Descended addition is commutative after metric separation. -/
theorem separatedAdd_comm (A : XBallTheoryModel.{u})
    (x y : A.SeparatedDirectedPoint) :
    A.separatedAdd x y = A.separatedAdd y x := by
  refine Quotient.inductionOn' x ?_
  intro xRepresentative
  refine Quotient.inductionOn' y ?_
  intro yRepresentative
  rcases xRepresentative with ⟨r, x⟩
  rcases yRepresentative with ⟨s, y⟩
  change A.separatedAdd (A.toSeparatedDirectedPoint ⟨r, x⟩)
      (A.toSeparatedDirectedPoint ⟨s, y⟩) =
    A.separatedAdd (A.toSeparatedDirectedPoint ⟨s, y⟩)
      (A.toSeparatedDirectedPoint ⟨r, x⟩)
  rw [A.separatedAdd_toSeparatedDirectedPoint,
    A.separatedAdd_toSeparatedDirectedPoint]
  let target := addCommTarget r s
  let hrs : r + s ≤ target :=
    le_add_of_nonneg_right (zero_le (s + r))
  let hsr : s + r ≤ target :=
    le_add_of_nonneg_left (zero_le (r + s))
  calc
    A.toSeparatedDirectedPoint (A.directedAdd ⟨r, x⟩ ⟨s, y⟩) =
      A.toSeparatedDirectedPoint
        ⟨target, A.model.inclusion hrs (A.model.add r s (x, y))⟩ :=
      (A.toSeparatedDirectedPoint_inclusion hrs
        (A.model.add r s (x, y))).symm
    _ = A.toSeparatedDirectedPoint
        ⟨target, A.model.inclusion hsr (A.model.add s r (y, x))⟩ := by
      rw [A.toSeparatedDirectedPoint_eq_iff]
      apply A.directedDistance_sameRadius_eq_zero
      exact dist_add_comm_eq_zero_of_sameCompleteTheory
        A.model A.sameCompleteTheory r s x y
    _ = A.toSeparatedDirectedPoint (A.directedAdd ⟨s, y⟩ ⟨r, x⟩) :=
      A.toSeparatedDirectedPoint_inclusion hsr
        (A.model.add s r (y, x))

/-- Left translation also preserves distance, by commutativity and the
right-translation isometry. -/
theorem dist_separatedAdd_left (A : XBallTheoryModel.{u})
    (x y z : A.SeparatedDirectedPoint) :
    dist (A.separatedAdd z x) (A.separatedAdd z y) = dist x y := by
  rw [A.separatedAdd_comm z x, A.separatedAdd_comm z y]
  exact A.dist_separatedAdd_right x y z

/-- Addition satisfies the standard two-variable metric estimate. -/
theorem dist_separatedAdd_le (A : XBallTheoryModel.{u})
    (x₁ x₂ y₁ y₂ : A.SeparatedDirectedPoint) :
    dist (A.separatedAdd x₁ y₁) (A.separatedAdd x₂ y₂) ≤
      dist x₁ x₂ + dist y₁ y₂ := by
  calc
    dist (A.separatedAdd x₁ y₁) (A.separatedAdd x₂ y₂) ≤
        dist (A.separatedAdd x₁ y₁) (A.separatedAdd x₂ y₁) +
          dist (A.separatedAdd x₂ y₁) (A.separatedAdd x₂ y₂) :=
      dist_triangle _ _ _
    _ = dist x₁ x₂ + dist y₁ y₂ := by
      rw [A.dist_separatedAdd_right, A.dist_separatedAdd_left]

/-- Descended addition is `2`-Lipschitz for the maximum product metric. -/
theorem separatedAdd_lipschitzWith (A : XBallTheoryModel.{u}) :
    LipschitzWith 2 (Function.uncurry A.separatedAdd) := by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
  change dist (A.separatedAdd x₁ y₁) (A.separatedAdd x₂ y₂) ≤
    ((2 : NNReal) : ℝ) * dist (x₁, y₁) (x₂, y₂)
  apply le_trans (A.dist_separatedAdd_le x₁ x₂ y₁ y₂)
  rw [Prod.dist_eq]
  have hx : dist x₁ x₂ ≤ max (dist x₁ x₂) (dist y₁ y₂) :=
    le_max_left _ _
  have hy : dist y₁ y₂ ≤ max (dist x₁ x₂) (dist y₁ y₂) :=
    le_max_right _ _
  norm_num
  linarith

/-- Descended addition is jointly uniformly continuous. -/
theorem separatedAdd_uniformContinuous₂ (A : XBallTheoryModel.{u}) :
    UniformContinuous₂ A.separatedAdd :=
  A.separatedAdd_lipschitzWith.uniformContinuous

/-- Descended addition is associative after metric separation. -/
theorem separatedAdd_assoc (A : XBallTheoryModel.{u})
    (x y z : A.SeparatedDirectedPoint) :
    A.separatedAdd (A.separatedAdd x y) z =
      A.separatedAdd x (A.separatedAdd y z) := by
  refine Quotient.inductionOn' x ?_
  intro xRepresentative
  refine Quotient.inductionOn' y ?_
  intro yRepresentative
  refine Quotient.inductionOn' z ?_
  intro zRepresentative
  rcases xRepresentative with ⟨r, x⟩
  rcases yRepresentative with ⟨s, y⟩
  rcases zRepresentative with ⟨t, z⟩
  change A.separatedAdd
      (A.separatedAdd (A.toSeparatedDirectedPoint ⟨r, x⟩)
        (A.toSeparatedDirectedPoint ⟨s, y⟩))
      (A.toSeparatedDirectedPoint ⟨t, z⟩) =
    A.separatedAdd (A.toSeparatedDirectedPoint ⟨r, x⟩)
      (A.separatedAdd (A.toSeparatedDirectedPoint ⟨s, y⟩)
        (A.toSeparatedDirectedPoint ⟨t, z⟩))
  rw [A.separatedAdd_toSeparatedDirectedPoint,
    A.separatedAdd_toSeparatedDirectedPoint,
    A.separatedAdd_toSeparatedDirectedPoint,
    A.separatedAdd_toSeparatedDirectedPoint]
  let target := addAssocTarget r s t
  let hleft : (r + s) + t ≤ target :=
    le_add_of_nonneg_right (zero_le (r + (s + t)))
  let hright : r + (s + t) ≤ target :=
    le_add_of_nonneg_left (zero_le ((r + s) + t))
  let leftValue := A.model.add (r + s) t (A.model.add r s (x, y), z)
  let rightValue := A.model.add r (s + t) (x, A.model.add s t (y, z))
  calc
    A.toSeparatedDirectedPoint
        (A.directedAdd (A.directedAdd ⟨r, x⟩ ⟨s, y⟩) ⟨t, z⟩) =
      A.toSeparatedDirectedPoint
        ⟨target, A.model.inclusion hleft leftValue⟩ :=
      (A.toSeparatedDirectedPoint_inclusion hleft leftValue).symm
    _ = A.toSeparatedDirectedPoint
        ⟨target, A.model.inclusion hright rightValue⟩ := by
      rw [A.toSeparatedDirectedPoint_eq_iff]
      apply A.directedDistance_sameRadius_eq_zero
      exact dist_add_assoc_eq_zero_of_sameCompleteTheory
        A.model A.sameCompleteTheory r s t x y z
    _ = A.toSeparatedDirectedPoint
        (A.directedAdd ⟨r, x⟩ (A.directedAdd ⟨s, y⟩ ⟨t, z⟩)) :=
      A.toSeparatedDirectedPoint_inclusion hright rightValue

noncomputable instance (A : XBallTheoryModel.{u}) :
    Zero A.SeparatedDirectedPoint where
  zero := A.separatedZero

noncomputable instance (A : XBallTheoryModel.{u}) :
    Neg A.SeparatedDirectedPoint where
  neg := A.separatedNeg

noncomputable instance (A : XBallTheoryModel.{u}) :
    Add A.SeparatedDirectedPoint where
  add := A.separatedAdd

/-- The metric-separated directed union is an additive commutative group.
Every group axiom used here was transferred from an explicit typed sentence
of the complete X ball theory. -/
noncomputable instance (A : XBallTheoryModel.{u}) :
    AddCommGroup A.SeparatedDirectedPoint :=
  { AddGroup.ofLeftAxioms
      (fun x y z ↦ A.separatedAdd_assoc x y z)
      (fun x ↦ A.separatedZero_add x)
      (fun x ↦ A.separatedNeg_add x) with
    add_comm := fun x y ↦ A.separatedAdd_comm x y }

/-- The syntax-transferred auxiliary-Hilbert parallelogram identity on two
separated points represented in one common radius. -/
theorem separatedHilbertValue_parallelogram_sameRadius
    (A : XBallTheoryModel.{u}) (r : ℚ≥0)
    (x y : A.model.Ball r) :
    A.separatedHilbertValue
          (A.toSeparatedDirectedPoint ⟨r, x⟩ +
            A.toSeparatedDirectedPoint ⟨r, y⟩) ^ 2 +
        A.separatedHilbertValue
          (A.toSeparatedDirectedPoint ⟨r, x⟩ -
            A.toSeparatedDirectedPoint ⟨r, y⟩) ^ 2 =
      2 *
        (A.separatedHilbertValue
              (A.toSeparatedDirectedPoint ⟨r, x⟩) ^ 2 +
          A.separatedHilbertValue
              (A.toSeparatedDirectedPoint ⟨r, y⟩) ^ 2) := by
  have hpar := parallelogram_of_sameCompleteTheory
    A.model A.sameCompleteTheory r x y
  change rationalBallMetricBound (r + r) ^ 2 *
      (((A.model.predicate (.hilbert (r + r))
          (A.model.add r r (x, y)) : ℝ) ^ 2) +
        ((A.model.predicate (.hilbert (r + r))
          (A.model.add r r (x, A.model.neg r y)) : ℝ) ^ 2)) =
    2 * rationalBallMetricBound r ^ 2 *
      (((A.model.predicate (.hilbert r) x : ℝ) ^ 2) +
        ((A.model.predicate (.hilbert r) y : ℝ) ^ 2)) at hpar
  change A.separatedHilbertValue
        (A.separatedAdd
          (A.toSeparatedDirectedPoint ⟨r, x⟩)
          (A.toSeparatedDirectedPoint ⟨r, y⟩)) ^ 2 +
      A.separatedHilbertValue
        (A.separatedAdd
          (A.toSeparatedDirectedPoint ⟨r, x⟩)
          (A.separatedNeg
            (A.toSeparatedDirectedPoint ⟨r, y⟩))) ^ 2 =
    2 *
      (A.separatedHilbertValue
            (A.toSeparatedDirectedPoint ⟨r, x⟩) ^ 2 +
        A.separatedHilbertValue
            (A.toSeparatedDirectedPoint ⟨r, y⟩) ^ 2)
  rw [A.separatedAdd_toSeparatedDirectedPoint,
    A.separatedNeg_toSeparatedDirectedPoint,
    A.separatedAdd_toSeparatedDirectedPoint]
  change
    (rationalBallMetricBound (r + r) *
        (A.model.predicate (.hilbert (r + r))
          (A.model.add r r (x, y)) : ℝ)) ^ 2 +
      (rationalBallMetricBound (r + r) *
        (A.model.predicate (.hilbert (r + r))
          (A.model.add r r (x, A.model.neg r y)) : ℝ)) ^ 2 =
    2 *
      ((rationalBallMetricBound r *
          (A.model.predicate (.hilbert r) x : ℝ)) ^ 2 +
        (rationalBallMetricBound r *
          (A.model.predicate (.hilbert r) y : ℝ)) ^ 2)
  nlinarith

/-- The auxiliary-Hilbert parallelogram identity on the entire separated
directed union.  Arbitrary representatives are first included into one
common radius. -/
theorem separatedHilbertValue_parallelogram
    (A : XBallTheoryModel.{u}) (x y : A.SeparatedDirectedPoint) :
    A.separatedHilbertValue (x + y) ^ 2 +
        A.separatedHilbertValue (x - y) ^ 2 =
      2 * (A.separatedHilbertValue x ^ 2 +
        A.separatedHilbertValue y ^ 2) := by
  refine Quotient.inductionOn' x ?_
  rintro ⟨r, x⟩
  refine Quotient.inductionOn' y ?_
  rintro ⟨s, y⟩
  let target := r + s
  let hx : r ≤ target := le_add_of_nonneg_right (zero_le s)
  let hy : s ≤ target := le_add_of_nonneg_left (zero_le r)
  have hpar := A.separatedHilbertValue_parallelogram_sameRadius target
    (A.model.inclusion hx x) (A.model.inclusion hy y)
  rw [A.toSeparatedDirectedPoint_inclusion hx x,
    A.toSeparatedDirectedPoint_inclusion hy y] at hpar
  exact hpar

/-- Scalar multiplication by one is the identity after metric separation. -/
theorem separatedOne_smul (A : XBallTheoryModel.{u})
    (x : A.SeparatedDirectedPoint) :
    A.separatedSmul 1 x = x := by
  refine Quotient.inductionOn' x ?_
  rintro ⟨r, x⟩
  change A.separatedSmul 1 (A.toSeparatedDirectedPoint ⟨r, x⟩) =
    A.toSeparatedDirectedPoint ⟨r, x⟩
  change A.toSeparatedDirectedPoint (A.directedSmul 1 ⟨r, x⟩) =
    A.toSeparatedDirectedPoint ⟨r, x⟩
  let target := oneSmulTarget r
  let hleft : (1 : ℚ).nnabs * r ≤ target :=
    le_add_of_nonneg_right (zero_le r)
  let hright : r ≤ target :=
    le_add_of_nonneg_left (zero_le ((1 : ℚ).nnabs * r))
  calc
    A.toSeparatedDirectedPoint (A.directedSmul 1 ⟨r, x⟩) =
      A.toSeparatedDirectedPoint
        ⟨target, A.model.inclusion hleft (A.model.smul 1 r x)⟩ :=
      (A.toSeparatedDirectedPoint_inclusion hleft
        (A.model.smul 1 r x)).symm
    _ = A.toSeparatedDirectedPoint
        ⟨target, A.model.inclusion hright x⟩ := by
      rw [A.toSeparatedDirectedPoint_eq_iff]
      apply A.directedDistance_sameRadius_eq_zero
      exact dist_one_smul_eq_zero_of_sameCompleteTheory
        A.model A.sameCompleteTheory r x
    _ = A.toSeparatedDirectedPoint ⟨r, x⟩ :=
      A.toSeparatedDirectedPoint_inclusion hright x

noncomputable instance (A : XBallTheoryModel.{u}) :
    SMul ℚ A.SeparatedDirectedPoint where
  smul := A.separatedSmul

@[simp] theorem separatedSmul_toSeparatedDirectedPoint
    (A : XBallTheoryModel.{u}) (q : ℚ) (x : A.DirectedPoint) :
    A.separatedSmul q (A.toSeparatedDirectedPoint x) =
      A.toSeparatedDirectedPoint (A.directedSmul q x) :=
  rfl

/-- The descended auxiliary Hilbert value is exactly homogeneous under the
canonical rational scalar action. -/
theorem separatedHilbertValue_smul
    (A : XBallTheoryModel.{u}) (q : ℚ)
    (x : A.SeparatedDirectedPoint) :
    A.separatedHilbertValue (q • x) =
      (q.nnabs : ℝ) * A.separatedHilbertValue x := by
  refine Quotient.inductionOn' x ?_
  intro representative
  change A.separatedHilbertValue
      (A.separatedSmul q
        (A.toSeparatedDirectedPoint representative)) =
    (q.nnabs : ℝ) *
      A.separatedHilbertValue
        (A.toSeparatedDirectedPoint representative)
  rw [A.separatedSmul_toSeparatedDirectedPoint,
    A.separatedHilbertValue_toSeparatedDirectedPoint,
    A.separatedHilbertValue_toSeparatedDirectedPoint]
  exact A.directedHilbertValue_smul q representative

/-- The fixed-scalar metric bound for representatives in one source radius. -/
theorem dist_separatedSmul_sameRadius_le (A : XBallTheoryModel.{u})
    (q : ℚ) (r : ℚ≥0) (x y : A.model.Ball r) :
    dist
        (A.separatedSmul q (A.toSeparatedDirectedPoint ⟨r, x⟩))
        (A.separatedSmul q (A.toSeparatedDirectedPoint ⟨r, y⟩)) ≤
      (q.nnabs : ℝ) *
        dist (A.toSeparatedDirectedPoint ⟨r, x⟩)
          (A.toSeparatedDirectedPoint ⟨r, y⟩) := by
  rw [A.separatedSmul_toSeparatedDirectedPoint,
    A.separatedSmul_toSeparatedDirectedPoint,
    A.dist_toSeparatedDirectedPoint,
    A.dist_toSeparatedDirectedPoint]
  change A.directedDistance
      ⟨q.nnabs * r, A.model.smul q r x⟩
      ⟨q.nnabs * r, A.model.smul q r y⟩ ≤
    (q.nnabs : ℝ) * A.directedDistance ⟨r, x⟩ ⟨r, y⟩
  rw [A.directedDistance_sameRadius, A.directedDistance_sameRadius]
  exact smul_rescaledDistance_le_of_sameCompleteTheory
    A.model A.sameCompleteTheory q r x y

/-- Every fixed rational scalar map satisfies its sharp metric bound on the
entire separated directed union. -/
theorem dist_separatedSmul_le (A : XBallTheoryModel.{u})
    (q : ℚ) (x y : A.SeparatedDirectedPoint) :
    dist (A.separatedSmul q x) (A.separatedSmul q y) ≤
      (q.nnabs : ℝ) * dist x y := by
  refine Quotient.inductionOn' x ?_
  intro xRepresentative
  refine Quotient.inductionOn' y ?_
  intro yRepresentative
  rcases xRepresentative with ⟨r, x⟩
  rcases yRepresentative with ⟨s, y⟩
  let target := r + s
  let hx : r ≤ target := le_add_of_nonneg_right (zero_le s)
  let hy : s ≤ target := le_add_of_nonneg_left (zero_le r)
  change dist
      (A.separatedSmul q (A.toSeparatedDirectedPoint ⟨r, x⟩))
      (A.separatedSmul q (A.toSeparatedDirectedPoint ⟨s, y⟩)) ≤
    (q.nnabs : ℝ) *
      dist (A.toSeparatedDirectedPoint ⟨r, x⟩)
        (A.toSeparatedDirectedPoint ⟨s, y⟩)
  rw [← A.toSeparatedDirectedPoint_inclusion hx x,
    ← A.toSeparatedDirectedPoint_inclusion hy y]
  exact A.dist_separatedSmul_sameRadius_le q target
    (A.model.inclusion hx x) (A.model.inclusion hy y)

/-- The nonnegative-real Lipschitz constant corresponding to `|q|`. -/
def rationalSmulLipschitzConstant (q : ℚ) : NNReal :=
  ⟨(q.nnabs : ℝ), NNRat.cast_nonneg q.nnabs⟩

@[simp] theorem coe_rationalSmulLipschitzConstant (q : ℚ) :
    (rationalSmulLipschitzConstant q : ℝ) = (q.nnabs : ℝ) :=
  rfl

/-- Multiplication by `q` on the separated union is `|q|`-Lipschitz. -/
theorem separatedSmul_lipschitzWith (A : XBallTheoryModel.{u}) (q : ℚ) :
    LipschitzWith (rationalSmulLipschitzConstant q) (A.separatedSmul q) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa using A.dist_separatedSmul_le q x y

theorem separatedSmul_uniformContinuous (A : XBallTheoryModel.{u}) (q : ℚ) :
    UniformContinuous (A.separatedSmul q) :=
  (A.separatedSmul_lipschitzWith q).uniformContinuous

/-- Rational scalar multiplication composes multiplicatively after metric
separation. -/
theorem separatedMul_smul (A : XBallTheoryModel.{u})
    (q p : ℚ) (x : A.SeparatedDirectedPoint) :
    A.separatedSmul (q * p) x =
      A.separatedSmul q (A.separatedSmul p x) := by
  refine Quotient.inductionOn' x ?_
  rintro ⟨r, x⟩
  change A.separatedSmul (q * p) (A.toSeparatedDirectedPoint ⟨r, x⟩) =
    A.separatedSmul q
      (A.separatedSmul p (A.toSeparatedDirectedPoint ⟨r, x⟩))
  rw [A.separatedSmul_toSeparatedDirectedPoint,
    A.separatedSmul_toSeparatedDirectedPoint,
    A.separatedSmul_toSeparatedDirectedPoint]
  let target := mulSmulTarget q p r
  let hleft : (q * p).nnabs * r ≤ target :=
    le_add_of_nonneg_right (zero_le (q.nnabs * (p.nnabs * r)))
  let hright : q.nnabs * (p.nnabs * r) ≤ target :=
    le_add_of_nonneg_left (zero_le ((q * p).nnabs * r))
  let leftValue := A.model.smul (q * p) r x
  let rightValue := A.model.smul q (p.nnabs * r) (A.model.smul p r x)
  calc
    A.toSeparatedDirectedPoint (A.directedSmul (q * p) ⟨r, x⟩) =
      A.toSeparatedDirectedPoint
        ⟨target, A.model.inclusion hleft leftValue⟩ :=
      (A.toSeparatedDirectedPoint_inclusion hleft leftValue).symm
    _ = A.toSeparatedDirectedPoint
        ⟨target, A.model.inclusion hright rightValue⟩ := by
      rw [A.toSeparatedDirectedPoint_eq_iff]
      apply A.directedDistance_sameRadius_eq_zero
      exact dist_mul_smul_eq_zero_of_sameCompleteTheory
        A.model A.sameCompleteTheory q p r x
    _ = A.toSeparatedDirectedPoint
        (A.directedSmul q (A.directedSmul p ⟨r, x⟩)) :=
      A.toSeparatedDirectedPoint_inclusion hright rightValue

/-- Rational scalar multiplication distributes over descended addition after
metric separation. -/
theorem separatedSmul_add (A : XBallTheoryModel.{u})
    (q : ℚ) (x y : A.SeparatedDirectedPoint) :
    A.separatedSmul q (A.separatedAdd x y) =
      A.separatedAdd (A.separatedSmul q x) (A.separatedSmul q y) := by
  refine Quotient.inductionOn' x ?_
  intro xRepresentative
  refine Quotient.inductionOn' y ?_
  intro yRepresentative
  rcases xRepresentative with ⟨r, x⟩
  rcases yRepresentative with ⟨s, y⟩
  change A.separatedSmul q
      (A.separatedAdd (A.toSeparatedDirectedPoint ⟨r, x⟩)
        (A.toSeparatedDirectedPoint ⟨s, y⟩)) =
    A.separatedAdd
      (A.separatedSmul q (A.toSeparatedDirectedPoint ⟨r, x⟩))
      (A.separatedSmul q (A.toSeparatedDirectedPoint ⟨s, y⟩))
  rw [A.separatedAdd_toSeparatedDirectedPoint,
    A.separatedSmul_toSeparatedDirectedPoint,
    A.separatedSmul_toSeparatedDirectedPoint,
    A.separatedSmul_toSeparatedDirectedPoint,
    A.separatedAdd_toSeparatedDirectedPoint]
  let target := smulAddTarget q r s
  let hleft : q.nnabs * (r + s) ≤ target :=
    le_add_of_nonneg_right (zero_le (q.nnabs * r + q.nnabs * s))
  let hright : q.nnabs * r + q.nnabs * s ≤ target :=
    le_add_of_nonneg_left (zero_le (q.nnabs * (r + s)))
  let leftValue := A.model.smul q (r + s) (A.model.add r s (x, y))
  let rightValue := A.model.add (q.nnabs * r) (q.nnabs * s)
    (A.model.smul q r x, A.model.smul q s y)
  calc
    A.toSeparatedDirectedPoint
        (A.directedSmul q (A.directedAdd ⟨r, x⟩ ⟨s, y⟩)) =
      A.toSeparatedDirectedPoint
        ⟨target, A.model.inclusion hleft leftValue⟩ :=
      (A.toSeparatedDirectedPoint_inclusion hleft leftValue).symm
    _ = A.toSeparatedDirectedPoint
        ⟨target, A.model.inclusion hright rightValue⟩ := by
      rw [A.toSeparatedDirectedPoint_eq_iff]
      apply A.directedDistance_sameRadius_eq_zero
      exact dist_smul_add_eq_zero_of_sameCompleteTheory
        A.model A.sameCompleteTheory q r s x y
    _ = A.toSeparatedDirectedPoint
        (A.directedAdd (A.directedSmul q ⟨r, x⟩)
          (A.directedSmul q ⟨s, y⟩)) :=
      A.toSeparatedDirectedPoint_inclusion hright rightValue

/-- Addition of rational scalars distributes over the descended scalar action
after metric separation. -/
theorem separatedAdd_smul (A : XBallTheoryModel.{u})
    (q p : ℚ) (x : A.SeparatedDirectedPoint) :
    A.separatedSmul (q + p) x =
      A.separatedAdd (A.separatedSmul q x) (A.separatedSmul p x) := by
  refine Quotient.inductionOn' x ?_
  rintro ⟨r, x⟩
  change A.separatedSmul (q + p) (A.toSeparatedDirectedPoint ⟨r, x⟩) =
    A.separatedAdd
      (A.separatedSmul q (A.toSeparatedDirectedPoint ⟨r, x⟩))
      (A.separatedSmul p (A.toSeparatedDirectedPoint ⟨r, x⟩))
  rw [A.separatedSmul_toSeparatedDirectedPoint,
    A.separatedSmul_toSeparatedDirectedPoint,
    A.separatedSmul_toSeparatedDirectedPoint,
    A.separatedAdd_toSeparatedDirectedPoint]
  let target := addSmulTarget q p r
  let hleft : (q + p).nnabs * r ≤ target :=
    le_add_of_nonneg_right (zero_le (q.nnabs * r + p.nnabs * r))
  let hright : q.nnabs * r + p.nnabs * r ≤ target :=
    le_add_of_nonneg_left (zero_le ((q + p).nnabs * r))
  let leftValue := A.model.smul (q + p) r x
  let rightValue := A.model.add (q.nnabs * r) (p.nnabs * r)
    (A.model.smul q r x, A.model.smul p r x)
  calc
    A.toSeparatedDirectedPoint (A.directedSmul (q + p) ⟨r, x⟩) =
      A.toSeparatedDirectedPoint
        ⟨target, A.model.inclusion hleft leftValue⟩ :=
      (A.toSeparatedDirectedPoint_inclusion hleft leftValue).symm
    _ = A.toSeparatedDirectedPoint
        ⟨target, A.model.inclusion hright rightValue⟩ := by
      rw [A.toSeparatedDirectedPoint_eq_iff]
      apply A.directedDistance_sameRadius_eq_zero
      exact dist_add_smul_eq_zero_of_sameCompleteTheory
        A.model A.sameCompleteTheory q p r x
    _ = A.toSeparatedDirectedPoint
        (A.directedAdd (A.directedSmul q ⟨r, x⟩)
          (A.directedSmul p ⟨r, x⟩)) :=
      A.toSeparatedDirectedPoint_inclusion hright rightValue

/-- The metric-separated directed union is a rational module. Every module
law is obtained from an explicit sentence of the complete X ball theory. -/
noncomputable instance (A : XBallTheoryModel.{u}) :
    Module ℚ A.SeparatedDirectedPoint :=
  Module.ofMinimalAxioms
    (fun q x y ↦ A.separatedSmul_add q x y)
    (fun q p x ↦ A.separatedAdd_smul q p x)
    (fun q p x ↦ A.separatedMul_smul q p x)
    (fun x ↦ A.separatedOne_smul x)

/-! ## Metric completion of the reconstructed rational module -/

/-- The complete one-sorted metric carrier reconstructed from all rational
ball sorts. Algebraic operations will be extended to this carrier after their
uniform-continuity estimates have been established. -/
abbrev CompletedDirectedPoint (A : XBallTheoryModel.{u}) :=
  UniformSpace.Completion A.SeparatedDirectedPoint

/-- Canonical embedding of the separated directed union into its metric
completion. -/
def toCompletedDirectedPoint (A : XBallTheoryModel.{u}) :
    A.SeparatedDirectedPoint → A.CompletedDirectedPoint :=
  fun x ↦ (x : UniformSpace.Completion A.SeparatedDirectedPoint)

/-- The canonical embedding into the completed reconstruction is an
isometry. -/
theorem toCompletedDirectedPoint_isometry (A : XBallTheoryModel.{u}) :
    Isometry A.toCompletedDirectedPoint :=
  UniformSpace.Completion.coe_isometry

@[simp] theorem dist_toCompletedDirectedPoint
    (A : XBallTheoryModel.{u}) (x y : A.SeparatedDirectedPoint) :
    dist (A.toCompletedDirectedPoint x) (A.toCompletedDirectedPoint y) =
      dist x y :=
  A.toCompletedDirectedPoint_isometry.dist_eq x y

/-- The auxiliary Hilbert value extended uniquely to the completed
reconstruction. -/
def completedHilbertValue (A : XBallTheoryModel.{u}) :
    A.CompletedDirectedPoint → ℝ :=
  UniformSpace.Completion.extension A.separatedHilbertValue

/-- The completed Hilbert value agrees exactly with the descended value on
the canonical dense image. -/
@[simp] theorem completedHilbertValue_toCompletedDirectedPoint
    (A : XBallTheoryModel.{u}) (x : A.SeparatedDirectedPoint) :
    A.completedHilbertValue (A.toCompletedDirectedPoint x) =
      A.separatedHilbertValue x := by
  exact UniformSpace.Completion.extension_coe
    A.separatedHilbertValue_uniformContinuous x

/-- The completed auxiliary Hilbert value retains the sharp Lipschitz
constant. -/
theorem completedHilbertValue_lipschitzWith
    (A : XBallTheoryModel.{u}) :
    LipschitzWith 1 A.completedHilbertValue :=
  A.separatedHilbertValue_lipschitzWith.completion_extension

theorem completedHilbertValue_uniformContinuous
    (A : XBallTheoryModel.{u}) :
    UniformContinuous A.completedHilbertValue :=
  A.completedHilbertValue_lipschitzWith.uniformContinuous

theorem completedHilbertValue_nonneg
    (A : XBallTheoryModel.{u}) (x : A.CompletedDirectedPoint) :
    0 ≤ A.completedHilbertValue x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le continuous_const
      A.completedHilbertValue_uniformContinuous.continuous) ?_
  intro y
  change 0 ≤ A.completedHilbertValue (A.toCompletedDirectedPoint y)
  rw [A.completedHilbertValue_toCompletedDirectedPoint]
  exact A.separatedHilbertValue_nonneg y

/-- The separated directed union is dense in the completed reconstruction. -/
theorem denseRange_toCompletedDirectedPoint (A : XBallTheoryModel.{u}) :
    DenseRange A.toCompletedDirectedPoint :=
  UniformSpace.Completion.denseRange_coe

/-- The reconstructed completed carrier is complete. -/
theorem completedDirectedPoint_completeSpace (A : XBallTheoryModel.{u}) :
    CompleteSpace A.CompletedDirectedPoint :=
  inferInstance

/-- Sortwise separability of the typed ball model implies separability of
the metric-separated directed union.  A countable dense family is obtained
by taking one dense sequence in every rational-radius sort. -/
theorem separatedDirectedPoint_separableSpace
    (A : XBallTheoryModel.{u})
    (hseparable : ∀ radius : ℚ≥0,
      IsSeparable (Set.univ : Set (A.model.Ball radius))) :
    SeparableSpace A.SeparatedDirectedPoint := by
  letI (radius : ℚ≥0) : SeparableSpace (A.model.Ball radius) :=
    TopologicalSpace.isSeparable_univ_iff.mp (hseparable radius)
  let densePoints : ℚ≥0 × ℕ → A.SeparatedDirectedPoint := fun index ↦
    A.toSeparatedDirectedPoint
      ⟨index.1, TopologicalSpace.denseSeq (A.model.Ball index.1) index.2⟩
  apply SeparableSpace.of_denseRange densePoints
  rw [Metric.denseRange_iff]
  intro point
  refine Quotient.inductionOn' point ?_
  rintro ⟨radius, x⟩ ε hε
  let scale : ℝ :=
    rationalBallMetricBound radius / A.model.sortBound radius
  have hscale : 0 < scale :=
    div_pos (rationalBallMetricBound_pos radius)
      (A.model.sortBound_pos radius)
  obtain ⟨n, hn⟩ :=
    (TopologicalSpace.denseRange_denseSeq (A.model.Ball radius)).exists_dist_lt
      x (div_pos hε hscale)
  refine ⟨(radius, n), ?_⟩
  change dist
      (A.toSeparatedDirectedPoint ⟨radius, x⟩)
      (A.toSeparatedDirectedPoint
        ⟨radius, TopologicalSpace.denseSeq (A.model.Ball radius) n⟩) < ε
  rw [A.dist_toSeparatedDirectedPoint, A.directedDistance_sameRadius]
  rw [show rationalBallMetricBound radius *
      (dist x (TopologicalSpace.denseSeq (A.model.Ball radius) n) /
        A.model.sortBound radius) =
      scale * dist x
        (TopologicalSpace.denseSeq (A.model.Ball radius) n) by
    unfold scale
    ring]
  exact (lt_div_iff₀' hscale).mp hn

/-- The completion of the reconstructed directed union is separable whenever
all typed radius sorts are separable. -/
theorem completedDirectedPoint_separableSpace
    (A : XBallTheoryModel.{u})
    (hseparable : ∀ radius : ℚ≥0,
      IsSeparable (Set.univ : Set (A.model.Ball radius))) :
    SeparableSpace A.CompletedDirectedPoint := by
  letI : SeparableSpace A.SeparatedDirectedPoint :=
    A.separatedDirectedPoint_separableSpace hseparable
  infer_instance

/-- The distinguished zero in the completed reconstruction.  This is the
canonical image of the separated zero and agrees definitionally with the
zero operation that Mathlib installs on a completion. -/
def completedZero (A : XBallTheoryModel.{u}) : A.CompletedDirectedPoint :=
  A.toCompletedDirectedPoint A.separatedZero

@[simp] theorem completedZero_eq_zero (A : XBallTheoryModel.{u}) :
    A.completedZero = 0 :=
  rfl

/-- Negation on the separated reconstruction is uniformly continuous.  It
is the already-controlled scalar map for the rational scalar `-1`. -/
theorem separatedNeg_uniformContinuous (A : XBallTheoryModel.{u}) :
    UniformContinuous A.separatedNeg := by
  have hfun : A.separatedNeg = A.separatedSmul (-1) := by
    funext x
    change -x = (-1 : ℚ) • x
    exact (neg_one_smul ℚ x).symm
  rw [hfun]
  exact A.separatedSmul_uniformContinuous (-1)

/-- The transferred additive laws and metric estimates make the separated
reconstruction a uniform additive group.  This is the sole topological
certificate needed by Mathlib to transport the `AddCommGroup` structure to
the completion. -/
noncomputable instance (A : XBallTheoryModel.{u}) :
    IsUniformAddGroup A.SeparatedDirectedPoint :=
  IsUniformAddGroup.mk' A.separatedAdd_uniformContinuous₂
    A.separatedNeg_uniformContinuous

/-- Every fixed rational scalar acts uniformly continuously on the separated
reconstruction.  Together with the already installed `Module ℚ` structure,
this lets Mathlib transport the full rational module structure to the
completion. -/
noncomputable instance (A : XBallTheoryModel.{u}) :
    UniformContinuousConstSMul ℚ A.SeparatedDirectedPoint where
  uniformContinuous_const_smul := A.separatedSmul_uniformContinuous

/-- Negation extended uniformly continuously to the completed
reconstruction. -/
def completedNeg (A : XBallTheoryModel.{u}) :
    A.CompletedDirectedPoint → A.CompletedDirectedPoint :=
  UniformSpace.Completion.map A.separatedNeg

/-- The explicit completed negation agrees with Mathlib's canonical
completion negation. -/
@[simp] theorem completedNeg_eq_neg (A : XBallTheoryModel.{u})
    (x : A.CompletedDirectedPoint) :
    A.completedNeg x = -x :=
  rfl

/-- Completed negation agrees exactly with descended negation on the dense
canonical image. -/
@[simp] theorem completedNeg_toCompletedDirectedPoint
    (A : XBallTheoryModel.{u}) (x : A.SeparatedDirectedPoint) :
    A.completedNeg (A.toCompletedDirectedPoint x) =
      A.toCompletedDirectedPoint (A.separatedNeg x) := by
  exact UniformSpace.Completion.map_coe A.separatedNeg_uniformContinuous x

/-- Completed negation remains uniformly continuous. -/
theorem completedNeg_uniformContinuous (A : XBallTheoryModel.{u}) :
    UniformContinuous A.completedNeg :=
  UniformSpace.Completion.uniformContinuous_map

/-- Addition extended jointly and uniformly continuously to the completed
reconstruction. -/
def completedAdd (A : XBallTheoryModel.{u}) :
    A.CompletedDirectedPoint → A.CompletedDirectedPoint →
      A.CompletedDirectedPoint :=
  UniformSpace.Completion.map₂ A.separatedAdd

/-- The explicit completed addition agrees with Mathlib's canonical
completion addition. -/
@[simp] theorem completedAdd_eq_add (A : XBallTheoryModel.{u})
    (x y : A.CompletedDirectedPoint) :
    A.completedAdd x y = x + y :=
  rfl

/-- Completed addition agrees exactly with descended addition on the dense
canonical image. -/
@[simp] theorem completedAdd_toCompletedDirectedPoint
    (A : XBallTheoryModel.{u}) (x y : A.SeparatedDirectedPoint) :
    A.completedAdd (A.toCompletedDirectedPoint x)
        (A.toCompletedDirectedPoint y) =
      A.toCompletedDirectedPoint (A.separatedAdd x y) := by
  exact UniformSpace.Completion.map₂_coe_coe
    x y A.separatedAdd A.separatedAdd_uniformContinuous₂

/-- Completed addition remains jointly uniformly continuous. -/
theorem completedAdd_uniformContinuous₂ (A : XBallTheoryModel.{u}) :
    UniformContinuous₂ A.completedAdd :=
  UniformSpace.Completion.uniformContinuous_map₂ A.separatedAdd

/-- Multiplication by a fixed rational scalar, extended to the completed
reconstruction. -/
def completedSmul (A : XBallTheoryModel.{u}) (q : ℚ) :
    A.CompletedDirectedPoint → A.CompletedDirectedPoint :=
  UniformSpace.Completion.map (A.separatedSmul q)

/-- The explicit fixed-scalar completion map is definitionally the scalar
action of the canonical completed rational module. -/
@[simp] theorem completedSmul_eq_smul (A : XBallTheoryModel.{u})
    (q : ℚ) (x : A.CompletedDirectedPoint) :
    A.completedSmul q x = q • x :=
  rfl

/-- Completed scalar multiplication agrees exactly with the descended scalar
map on the canonical dense image. -/
@[simp] theorem completedSmul_toCompletedDirectedPoint
    (A : XBallTheoryModel.{u}) (q : ℚ)
    (x : A.SeparatedDirectedPoint) :
    A.completedSmul q (A.toCompletedDirectedPoint x) =
      A.toCompletedDirectedPoint (A.separatedSmul q x) := by
  exact UniformSpace.Completion.map_coe
    (A.separatedSmul_uniformContinuous q) x

/-- Every completed fixed-scalar map is uniformly continuous. -/
theorem completedSmul_uniformContinuous
    (A : XBallTheoryModel.{u}) (q : ℚ) :
    UniformContinuous (A.completedSmul q) :=
  UniformSpace.Completion.uniformContinuous_map

/-- The completed auxiliary Hilbert value is exactly homogeneous under every
rational scalar. -/
theorem completedHilbertValue_smul_rat
    (A : XBallTheoryModel.{u}) (q : ℚ)
    (x : A.CompletedDirectedPoint) :
    A.completedHilbertValue (q • x) =
      (q.nnabs : ℝ) * A.completedHilbertValue x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq
      (A.completedHilbertValue_uniformContinuous.continuous.comp
        (A.completedSmul_uniformContinuous q).continuous)
      (continuous_const.mul
        A.completedHilbertValue_uniformContinuous.continuous)) ?_
  intro y
  change A.completedHilbertValue
      (A.completedSmul q (A.toCompletedDirectedPoint y)) =
    (q.nnabs : ℝ) *
      A.completedHilbertValue (A.toCompletedDirectedPoint y)
  rw [A.completedSmul_toCompletedDirectedPoint,
    A.completedHilbertValue_toCompletedDirectedPoint,
    A.completedHilbertValue_toCompletedDirectedPoint]
  exact A.separatedHilbertValue_smul q y

/-- The syntax-transferred parallelogram identity extends from the dense
separated union to the completed auxiliary Hilbert value. -/
theorem completedHilbertValue_parallelogram
    (A : XBallTheoryModel.{u}) (x y : A.CompletedDirectedPoint) :
    A.completedHilbertValue (x + y) ^ 2 +
        A.completedHilbertValue (x - y) ^ 2 =
      2 * (A.completedHilbertValue x ^ 2 +
        A.completedHilbertValue y ^ 2) := by
  let hH : Continuous A.completedHilbertValue :=
    A.completedHilbertValue_uniformContinuous.continuous
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_eq
      (((hH.comp (continuous_fst.add continuous_snd)).pow 2).add
        ((hH.comp (continuous_fst.sub continuous_snd)).pow 2))
      (continuous_const.mul
        (((hH.comp continuous_fst).pow 2).add
          ((hH.comp continuous_snd).pow 2)))) ?_
  intro x y
  rw [sub_eq_add_neg,
    ← A.completedAdd_eq_add, ← A.completedNeg_eq_neg,
    ← A.completedAdd_eq_add]
  change A.completedHilbertValue
        (A.completedAdd
          (A.toCompletedDirectedPoint x)
          (A.toCompletedDirectedPoint y)) ^ 2 +
      A.completedHilbertValue
        (A.completedAdd
          (A.toCompletedDirectedPoint x)
          (A.completedNeg (A.toCompletedDirectedPoint y))) ^ 2 =
    2 *
      (A.completedHilbertValue (A.toCompletedDirectedPoint x) ^ 2 +
        A.completedHilbertValue (A.toCompletedDirectedPoint y) ^ 2)
  rw [A.completedAdd_toCompletedDirectedPoint,
    A.completedNeg_toCompletedDirectedPoint,
    A.completedAdd_toCompletedDirectedPoint,
    A.completedHilbertValue_toCompletedDirectedPoint,
    A.completedHilbertValue_toCompletedDirectedPoint,
    A.completedHilbertValue_toCompletedDirectedPoint,
    A.completedHilbertValue_toCompletedDirectedPoint]
  exact A.separatedHilbertValue_parallelogram x y

/-- Completion preserves the sharp `|q|` Lipschitz bound. -/
theorem completedSmul_lipschitzWith
    (A : XBallTheoryModel.{u}) (q : ℚ) :
    LipschitzWith (rationalSmulLipschitzConstant q) (A.completedSmul q) :=
  (A.separatedSmul_lipschitzWith q).completion_map

/-! ## The canonical completed norm -/

/-- Left translation preserves the completed metric exactly.  The equality
is transported from the dense separated union by three-variable completion
induction. -/
theorem dist_completedAdd_left (A : XBallTheoryModel.{u})
    (x y z : A.CompletedDirectedPoint) :
    dist (z + x) (z + y) = dist x y := by
  refine UniformSpace.Completion.induction_on₃ x y z
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro x y z
  change dist
      (A.completedAdd (A.toCompletedDirectedPoint z)
        (A.toCompletedDirectedPoint x))
      (A.completedAdd (A.toCompletedDirectedPoint z)
        (A.toCompletedDirectedPoint y)) =
    dist (A.toCompletedDirectedPoint x) (A.toCompletedDirectedPoint y)
  rw [A.completedAdd_toCompletedDirectedPoint,
    A.completedAdd_toCompletedDirectedPoint,
    A.dist_toCompletedDirectedPoint, A.dist_toCompletedDirectedPoint]
  exact A.dist_separatedAdd_left x y z

/-- The completed norm is its translation-invariant distance from zero. -/
noncomputable instance (A : XBallTheoryModel.{u}) :
    Norm A.CompletedDirectedPoint where
  norm x := dist 0 x

/-- The reconstructed completed carrier is canonically a normed additive
commutative group, with its existing completion metric unchanged. -/
noncomputable instance (A : XBallTheoryModel.{u}) :
    NormedAddCommGroup A.CompletedDirectedPoint :=
  NormedAddCommGroup.ofAddDist (fun _ ↦ rfl)
    (fun x y z ↦ (A.dist_completedAdd_left x y z).ge)

/-- The reconstructed norm is definitionally distance from zero. -/
@[simp] theorem norm_completedDirectedPoint
    (A : XBallTheoryModel.{u}) (x : A.CompletedDirectedPoint) :
    ‖x‖ = dist 0 x :=
  rfl

/-- On the canonical dense image, the reconstructed norm is exactly the
separated distance from zero. -/
@[simp] theorem norm_toCompletedDirectedPoint
    (A : XBallTheoryModel.{u}) (x : A.SeparatedDirectedPoint) :
    ‖A.toCompletedDirectedPoint x‖ = dist x A.separatedZero := by
  rw [A.norm_completedDirectedPoint, ← A.completedZero_eq_zero]
  unfold completedZero
  rw [A.dist_toCompletedDirectedPoint, dist_comm]

/-- The completed auxiliary Hilbert value is bounded above by the
reconstructed norm. -/
theorem completedHilbertValue_le_norm
    (A : XBallTheoryModel.{u}) (x : A.CompletedDirectedPoint) :
    A.completedHilbertValue x ≤ ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le A.completedHilbertValue_uniformContinuous.continuous
      continuous_norm) ?_
  intro y
  change A.completedHilbertValue (A.toCompletedDirectedPoint y) ≤
    ‖A.toCompletedDirectedPoint y‖
  rw [A.completedHilbertValue_toCompletedDirectedPoint,
    A.norm_toCompletedDirectedPoint]
  exact A.separatedHilbertValue_le_dist_zero y

/-- The reconstructed norm is bounded above by `sqrt 3` times the completed
auxiliary Hilbert value. -/
theorem norm_le_sqrtThree_mul_completedHilbertValue
    (A : XBallTheoryModel.{u}) (x : A.CompletedDirectedPoint) :
    ‖x‖ ≤ Real.sqrt 3 * A.completedHilbertValue x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le continuous_norm
      (continuous_const.mul
        A.completedHilbertValue_uniformContinuous.continuous)) ?_
  intro y
  change ‖A.toCompletedDirectedPoint y‖ ≤
    Real.sqrt 3 *
      A.completedHilbertValue (A.toCompletedDirectedPoint y)
  rw [A.norm_toCompletedDirectedPoint,
    A.completedHilbertValue_toCompletedDirectedPoint]
  exact A.dist_zero_le_sqrtThree_mul_separatedHilbertValue y

/-- Rational scalar multiplication satisfies the sharp norm upper bound on
the reconstructed completion.  The estimate is the completed form of the
typed ball language's exact `|q|` Lipschitz modulus. -/
theorem norm_completedSmul_le
    (A : XBallTheoryModel.{u}) (q : ℚ)
    (x : A.CompletedDirectedPoint) :
    ‖q • x‖ ≤ ‖q‖ * ‖x‖ := by
  have h := (A.completedSmul_lipschitzWith q).dist_le_mul x 0
  rw [A.completedSmul_eq_smul, A.completedSmul_eq_smul, smul_zero] at h
  have hq : (rationalSmulLipschitzConstant q : ℝ) = ‖q‖ := by
    rw [coe_rationalSmulLipschitzConstant]
    rw [← Rat.norm_cast_real, Real.norm_eq_abs]
    norm_cast
  rw [dist_zero_right, dist_zero_right, hq] at h
  exact h

/-- The reconstructed completion is canonically a normed rational vector
space.  Mathlib derives the reverse scalar inequality from the displayed
upper bound by applying it to the inverse of a nonzero scalar. -/
noncomputable instance (A : XBallTheoryModel.{u}) :
    NormedSpace ℚ A.CompletedDirectedPoint where
  norm_smul_le := A.norm_completedSmul_le

/-- Rational scalar multiplication scales the reconstructed norm exactly. -/
theorem norm_completedSmul
    (A : XBallTheoryModel.{u}) (q : ℚ)
    (x : A.CompletedDirectedPoint) :
    ‖q • x‖ = ‖q‖ * ‖x‖ :=
  norm_smul q x

/-! ## Continuous extension of rational scalars -/

/-- For a fixed completed vector, its rational-scalar orbit is Lipschitz as a
function of the scalar. -/
theorem completedRationalSmul_lipschitzWith
    (A : XBallTheoryModel.{u}) (x : A.CompletedDirectedPoint) :
    LipschitzWith ‖x‖₊ (fun q : ℚ ↦ q • x) := by
  apply LipschitzWith.of_dist_le_mul
  intro q p
  rw [dist_eq_norm, ← sub_smul, A.norm_completedSmul, dist_eq_norm]
  simp only [coe_nnnorm]
  exact le_of_eq (mul_comm _ _)

/-- Real scalar multiplication, defined as the unique continuous extension of
the rational scalar orbit along the dense embedding `ℚ → ℝ`. -/
def completedRealSmul (A : XBallTheoryModel.{u})
    (r : ℝ) (x : A.CompletedDirectedPoint) : A.CompletedDirectedPoint :=
  Rat.isDenseEmbedding_coe_real.extend (fun q : ℚ ↦ q • x) r

/-- The extended real-scalar orbit remains uniformly continuous in its scalar
argument. -/
theorem completedRealSmul_uniformContinuous
    (A : XBallTheoryModel.{u}) (x : A.CompletedDirectedPoint) :
    UniformContinuous (fun r : ℝ ↦ A.completedRealSmul r x) := by
  unfold completedRealSmul
  exact uniformContinuous_uniformly_extend
    Rat.isUniformEmbedding_coe_real.isUniformInducing Rat.denseRange_cast
    (A.completedRationalSmul_lipschitzWith x).uniformContinuous

/-- The real extension agrees exactly with the original rational action on
the dense rational subfield. -/
theorem completedRealSmul_ratCast
    (A : XBallTheoryModel.{u}) (q : ℚ)
    (x : A.CompletedDirectedPoint) :
    A.completedRealSmul (q : ℝ) x = q • x := by
  unfold completedRealSmul
  exact Rat.isDenseEmbedding_coe_real.extend_eq
    (A.completedRationalSmul_lipschitzWith x).continuous q

/-- The canonical real scalar operation on the reconstructed completion. -/
noncomputable instance (A : XBallTheoryModel.{u}) :
    SMul ℝ A.CompletedDirectedPoint where
  smul := A.completedRealSmul

/-- Real scalar multiplication restricts to the pre-existing rational module
action. -/
@[simp] theorem real_smul_ratCast
    (A : XBallTheoryModel.{u}) (q : ℚ)
    (x : A.CompletedDirectedPoint) :
    (q : ℝ) • x = q • x :=
  A.completedRealSmul_ratCast q x

/-- For every fixed completed vector, the installed real scalar action is
uniformly continuous in the scalar. -/
theorem realSmul_uniformContinuous_fixed
    (A : XBallTheoryModel.{u}) (x : A.CompletedDirectedPoint) :
    UniformContinuous (fun r : ℝ ↦ r • x) :=
  A.completedRealSmul_uniformContinuous x

/-- Extended real scalar multiplication distributes over vector addition. -/
theorem completedRealSmul_add
    (A : XBallTheoryModel.{u}) (r : ℝ)
    (x y : A.CompletedDirectedPoint) :
    r • (x + y) = r • x + r • y := by
  refine Rat.denseRange_cast.induction_on r
    (isClosed_eq
      (A.realSmul_uniformContinuous_fixed (x + y)).continuous
      ((A.realSmul_uniformContinuous_fixed x).continuous.add
        (A.realSmul_uniformContinuous_fixed y).continuous)) ?_
  intro q
  rw [A.real_smul_ratCast, A.real_smul_ratCast, A.real_smul_ratCast]
  exact smul_add q x y

/-- Extended real scalar multiplication distributes over scalar addition. -/
theorem completedRealAdd_smul
    (A : XBallTheoryModel.{u}) (r s : ℝ)
    (x : A.CompletedDirectedPoint) :
    (r + s) • x = r • x + s • x := by
  refine Rat.denseRange_cast.induction_on₂
    (isClosed_eq
      ((A.realSmul_uniformContinuous_fixed x).continuous.comp
        (continuous_fst.add continuous_snd))
      (((A.realSmul_uniformContinuous_fixed x).continuous.comp continuous_fst).add
        ((A.realSmul_uniformContinuous_fixed x).continuous.comp continuous_snd))) ?_ r s
  intro q p
  rw [← Rat.cast_add, A.real_smul_ratCast,
    A.real_smul_ratCast, A.real_smul_ratCast]
  exact add_smul q p x

/-- Multiplication first by a real scalar and then by a rational scalar agrees
with multiplication by their product. -/
theorem ratCast_mul_completedRealSmul
    (A : XBallTheoryModel.{u}) (q : ℚ) (r : ℝ)
    (x : A.CompletedDirectedPoint) :
    ((q : ℝ) * r) • x = q • (r • x) := by
  have hq : Continuous (fun y : A.CompletedDirectedPoint ↦ q • y) := by
    simpa only [A.completedSmul_eq_smul] using
      (A.completedSmul_lipschitzWith q).continuous
  refine Rat.denseRange_cast.induction_on r
    (isClosed_eq
      ((A.realSmul_uniformContinuous_fixed x).continuous.comp
        (continuous_const.mul continuous_id))
      (hq.comp (A.realSmul_uniformContinuous_fixed x).continuous)) ?_
  intro p
  rw [← Rat.cast_mul, A.real_smul_ratCast, A.real_smul_ratCast]
  exact mul_smul q p x

/-- Extended real scalar multiplication is associative. -/
theorem completedRealMul_smul
    (A : XBallTheoryModel.{u}) (r s : ℝ)
    (x : A.CompletedDirectedPoint) :
    (r * s) • x = r • (s • x) := by
  refine Rat.denseRange_cast.induction_on r
    (isClosed_eq
      ((A.realSmul_uniformContinuous_fixed x).continuous.comp
        (continuous_id.mul continuous_const))
      (A.realSmul_uniformContinuous_fixed (s • x)).continuous) ?_
  intro q
  rw [A.real_smul_ratCast]
  exact A.ratCast_mul_completedRealSmul q s x

/-- Scalar multiplication by real one is the identity. -/
theorem completedRealOne_smul
    (A : XBallTheoryModel.{u}) (x : A.CompletedDirectedPoint) :
    (1 : ℝ) • x = x := by
  simpa using A.real_smul_ratCast 1 x

/-- The completed reconstruction is canonically a real vector space. -/
noncomputable instance (A : XBallTheoryModel.{u}) :
    Module ℝ A.CompletedDirectedPoint :=
  Module.ofMinimalAxioms
    (fun r x y ↦ A.completedRealSmul_add r x y)
    (fun r s x ↦ A.completedRealAdd_smul r s x)
    (fun r s x ↦ A.completedRealMul_smul r s x)
    (fun x ↦ A.completedRealOne_smul x)

/-- The continuously extended real action scales the reconstructed norm
exactly.  The identity is extended from the dense rational subfield. -/
theorem norm_completedRealSmul
    (A : XBallTheoryModel.{u}) (r : ℝ)
    (x : A.CompletedDirectedPoint) :
    ‖r • x‖ = ‖r‖ * ‖x‖ := by
  refine Rat.denseRange_cast.induction_on r
    (isClosed_eq
      (A.realSmul_uniformContinuous_fixed x).continuous.norm
      (continuous_norm.mul continuous_const)) ?_
  intro q
  rw [A.real_smul_ratCast, A.norm_completedSmul, Rat.norm_cast_real]

/-- The reconstructed completion is canonically a real normed space.  Since
the underlying metric completion is already complete, this is the desired
real Banach carrier. -/
noncomputable instance (A : XBallTheoryModel.{u}) :
    NormedSpace ℝ A.CompletedDirectedPoint where
  norm_smul_le r x := (A.norm_completedRealSmul r x).le

/-- Rational homogeneity and continuity extend the completed auxiliary
Hilbert value to exact homogeneity under every real scalar. -/
theorem completedHilbertValue_smul_real
    (A : XBallTheoryModel.{u}) (r : ℝ)
    (x : A.CompletedDirectedPoint) :
    A.completedHilbertValue (r • x) =
      ‖r‖ * A.completedHilbertValue x := by
  refine Rat.denseRange_cast.induction_on r
    (isClosed_eq
      (A.completedHilbertValue_uniformContinuous.continuous.comp
        (A.realSmul_uniformContinuous_fixed x).continuous)
      (continuous_norm.mul continuous_const)) ?_
  intro q
  rw [A.real_smul_ratCast, A.completedHilbertValue_smul_rat]
  congr 1
  rw [Real.norm_eq_abs]
  norm_cast

/-! ## The auxiliary Hilbert renorming carrier -/

/-- The completed auxiliary Hilbert value vanishes exactly at zero. -/
theorem completedHilbertValue_eq_zero_iff
    (A : XBallTheoryModel.{u}) (x : A.CompletedDirectedPoint) :
    A.completedHilbertValue x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hnorm_le := A.norm_le_sqrtThree_mul_completedHilbertValue x
    rw [hx, mul_zero] at hnorm_le
    exact norm_eq_zero.mp (le_antisymm hnorm_le (norm_nonneg x))
  · intro hx
    subst x
    exact le_antisymm
      (by simpa using A.completedHilbertValue_le_norm 0)
      (A.completedHilbertValue_nonneg 0)

/-- A separate carrier for the reconstructed vector space equipped with its
auxiliary Hilbert norm.  Keeping a distinct type prevents collision with the
already installed Banach norm. -/
structure AuxiliaryHilbertCarrier (A : XBallTheoryModel.{u}) where
  toCompletedDirectedPoint : A.CompletedDirectedPoint

/-- The auxiliary carrier is canonically equivalent to the reconstructed
Banach carrier as a plain type. -/
def auxiliaryHilbertCarrierEquiv (A : XBallTheoryModel.{u}) :
    A.AuxiliaryHilbertCarrier ≃ A.CompletedDirectedPoint where
  toFun := AuxiliaryHilbertCarrier.toCompletedDirectedPoint
  invFun := fun x ↦ ⟨x⟩
  left_inv := fun x ↦ by cases x; rfl
  right_inv := fun _ ↦ rfl

noncomputable instance (A : XBallTheoryModel.{u}) :
    AddCommGroup A.AuxiliaryHilbertCarrier :=
  Equiv.addCommGroup A.auxiliaryHilbertCarrierEquiv

noncomputable instance (A : XBallTheoryModel.{u}) :
    Module ℝ A.AuxiliaryHilbertCarrier :=
  Equiv.module ℝ A.auxiliaryHilbertCarrierEquiv

/-- The transported additive structure makes the carrier equivalence additive. -/
noncomputable def auxiliaryHilbertCarrierAddEquiv (A : XBallTheoryModel.{u}) :
    A.AuxiliaryHilbertCarrier ≃+ A.CompletedDirectedPoint :=
  Equiv.addEquiv A.auxiliaryHilbertCarrierEquiv

/-- The transported module structure makes the carrier equivalence real-linear. -/
noncomputable def auxiliaryHilbertCarrierLinearEquiv (A : XBallTheoryModel.{u}) :
    A.AuxiliaryHilbertCarrier ≃ₗ[ℝ] A.CompletedDirectedPoint :=
  Equiv.linearEquiv ℝ A.auxiliaryHilbertCarrierEquiv

/-- The norm operation on the auxiliary carrier is exactly the completed
Hilbert value.  Its triangle inequality will be obtained from polarization
in the next layer. -/
noncomputable instance (A : XBallTheoryModel.{u}) :
    Norm A.AuxiliaryHilbertCarrier where
  norm x := A.completedHilbertValue x.toCompletedDirectedPoint

@[simp] theorem norm_auxiliaryHilbertCarrier
    (A : XBallTheoryModel.{u}) (x : A.AuxiliaryHilbertCarrier) :
    ‖x‖ = A.completedHilbertValue x.toCompletedDirectedPoint :=
  rfl

@[simp] theorem auxiliaryHilbertCarrierEquiv_apply
    (A : XBallTheoryModel.{u}) (x : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryHilbertCarrierEquiv x = x.toCompletedDirectedPoint :=
  rfl

theorem norm_auxiliaryHilbertCarrier_nonneg
    (A : XBallTheoryModel.{u}) (x : A.AuxiliaryHilbertCarrier) :
    0 ≤ ‖x‖ :=
  A.completedHilbertValue_nonneg x.toCompletedDirectedPoint

theorem norm_auxiliaryHilbertCarrier_eq_zero_iff
    (A : XBallTheoryModel.{u}) (x : A.AuxiliaryHilbertCarrier) :
    ‖x‖ = 0 ↔ x = 0 := by
  rw [A.norm_auxiliaryHilbertCarrier,
    A.completedHilbertValue_eq_zero_iff]
  constructor
  · intro hx
    apply A.auxiliaryHilbertCarrierEquiv.injective
    simpa using hx
  · intro hx
    subst x
    rfl

theorem norm_auxiliaryHilbertCarrier_smul
    (A : XBallTheoryModel.{u}) (r : ℝ)
    (x : A.AuxiliaryHilbertCarrier) :
    ‖r • x‖ = ‖r‖ * ‖x‖ := by
  change A.completedHilbertValue
      (A.auxiliaryHilbertCarrierEquiv (r • x)) =
    ‖r‖ * A.completedHilbertValue
      (A.auxiliaryHilbertCarrierEquiv x)
  rw [show A.auxiliaryHilbertCarrierEquiv (r • x) =
      r • A.auxiliaryHilbertCarrierEquiv x by
    exact A.auxiliaryHilbertCarrierLinearEquiv.map_smul r x]
  exact A.completedHilbertValue_smul_real r
    (A.auxiliaryHilbertCarrierEquiv x)

theorem norm_auxiliaryHilbertCarrier_le_original
    (A : XBallTheoryModel.{u}) (x : A.AuxiliaryHilbertCarrier) :
    ‖x‖ ≤ ‖x.toCompletedDirectedPoint‖ :=
  A.completedHilbertValue_le_norm x.toCompletedDirectedPoint

theorem original_norm_le_sqrtThree_mul_auxiliaryHilbertCarrier
    (A : XBallTheoryModel.{u}) (x : A.AuxiliaryHilbertCarrier) :
    ‖x.toCompletedDirectedPoint‖ ≤ Real.sqrt 3 * ‖x‖ :=
  A.norm_le_sqrtThree_mul_completedHilbertValue
    x.toCompletedDirectedPoint

/-- The auxiliary norm operation satisfies the parallelogram identity. -/
theorem norm_auxiliaryHilbertCarrier_parallelogram
    (A : XBallTheoryModel.{u}) (x y : A.AuxiliaryHilbertCarrier) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 =
      2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  change A.completedHilbertValue
        (A.auxiliaryHilbertCarrierEquiv (x + y)) ^ 2 +
      A.completedHilbertValue
        (A.auxiliaryHilbertCarrierEquiv (x - y)) ^ 2 =
    2 *
      (A.completedHilbertValue (A.auxiliaryHilbertCarrierEquiv x) ^ 2 +
        A.completedHilbertValue (A.auxiliaryHilbertCarrierEquiv y) ^ 2)
  rw [show A.auxiliaryHilbertCarrierEquiv (x + y) =
      A.auxiliaryHilbertCarrierEquiv x +
        A.auxiliaryHilbertCarrierEquiv y by
    exact A.auxiliaryHilbertCarrierAddEquiv.map_add x y,
    show A.auxiliaryHilbertCarrierEquiv (x - y) =
      A.auxiliaryHilbertCarrierEquiv x -
        A.auxiliaryHilbertCarrierEquiv y by
    exact A.auxiliaryHilbertCarrierAddEquiv.map_sub x y]
  exact A.completedHilbertValue_parallelogram
    (A.auxiliaryHilbertCarrierEquiv x)
    (A.auxiliaryHilbertCarrierEquiv y)

/-! ## Real polarization of the auxiliary norm -/

@[simp] theorem norm_auxiliaryHilbertCarrier_zero
    (A : XBallTheoryModel.{u}) :
    ‖(0 : A.AuxiliaryHilbertCarrier)‖ = 0 :=
  (A.norm_auxiliaryHilbertCarrier_eq_zero_iff 0).2 rfl

@[simp] theorem norm_auxiliaryHilbertCarrier_neg
    (A : XBallTheoryModel.{u}) (x : A.AuxiliaryHilbertCarrier) :
    ‖-x‖ = ‖x‖ := by
  simpa using A.norm_auxiliaryHilbertCarrier_smul (-1) x

/-- The real polarization associated to the reconstructed auxiliary norm. -/
noncomputable def auxiliaryPolarization
    (A : XBallTheoryModel.{u})
    (x y : A.AuxiliaryHilbertCarrier) : ℝ :=
  (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2) / 4

/-- Real polarization is symmetric. -/
theorem auxiliaryPolarization_comm
    (A : XBallTheoryModel.{u})
    (x y : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryPolarization x y = A.auxiliaryPolarization y x := by
  unfold auxiliaryPolarization
  rw [add_comm x y,
    show y - x = -(x - y) by abel,
    A.norm_auxiliaryHilbertCarrier_neg]

/-- Polarization recovers the square of the auxiliary norm on the diagonal. -/
@[simp] theorem auxiliaryPolarization_self
    (A : XBallTheoryModel.{u})
    (x : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryPolarization x x = ‖x‖ ^ 2 := by
  unfold auxiliaryPolarization
  rw [sub_self, A.norm_auxiliaryHilbertCarrier_zero,
    show x + x = (2 : ℝ) • x by module,
    A.norm_auxiliaryHilbertCarrier_smul]
  norm_num
  ring

@[simp] theorem auxiliaryPolarization_zero_left
    (A : XBallTheoryModel.{u})
    (x : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryPolarization 0 x = 0 := by
  unfold auxiliaryPolarization
  rw [zero_add, zero_sub, A.norm_auxiliaryHilbertCarrier_neg]
  ring

@[simp] theorem auxiliaryPolarization_zero_right
    (A : XBallTheoryModel.{u})
    (x : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryPolarization x 0 = 0 := by
  rw [A.auxiliaryPolarization_comm]
  exact A.auxiliaryPolarization_zero_left x

/-- Diagonal polarization is nonnegative. -/
theorem auxiliaryPolarization_self_nonneg
    (A : XBallTheoryModel.{u})
    (x : A.AuxiliaryHilbertCarrier) :
    0 ≤ A.auxiliaryPolarization x x := by
  rw [A.auxiliaryPolarization_self]
  positivity

/-- Diagonal polarization vanishes exactly at the zero vector. -/
@[simp] theorem auxiliaryPolarization_self_eq_zero_iff
    (A : XBallTheoryModel.{u})
    (x : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryPolarization x x = 0 ↔ x = 0 := by
  rw [A.auxiliaryPolarization_self, sq_eq_zero_iff,
    A.norm_auxiliaryHilbertCarrier_eq_zero_iff]

/-- Polarization changes sign when its first argument is negated. -/
theorem auxiliaryPolarization_neg_left
    (A : XBallTheoryModel.{u})
    (x y : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryPolarization (-x) y = -A.auxiliaryPolarization x y := by
  unfold auxiliaryPolarization
  rw [show -x + y = -(x - y) by abel,
    show -x - y = -(x + y) by abel,
    A.norm_auxiliaryHilbertCarrier_neg,
    A.norm_auxiliaryHilbertCarrier_neg]
  ring

/-- Polarization changes sign when its second argument is negated. -/
theorem auxiliaryPolarization_neg_right
    (A : XBallTheoryModel.{u})
    (x y : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryPolarization x (-y) = -A.auxiliaryPolarization x y := by
  rw [A.auxiliaryPolarization_comm,
    A.auxiliaryPolarization_neg_left,
    A.auxiliaryPolarization_comm]

/-- The Jordan--von Neumann four-parallelogram calculation: polarization is
additive in its first argument. -/
theorem auxiliaryPolarization_add_left
    (A : XBallTheoryModel.{u})
    (x y z : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryPolarization (x + y) z =
      A.auxiliaryPolarization x z + A.auxiliaryPolarization y z := by
  unfold auxiliaryPolarization
  have h1 := A.norm_auxiliaryHilbertCarrier_parallelogram
    (x + y + z) (x - z)
  have h2 := A.norm_auxiliaryHilbertCarrier_parallelogram
    (x + y - z) (x + z)
  have h3 := A.norm_auxiliaryHilbertCarrier_parallelogram
    (y + z) z
  have h4 := A.norm_auxiliaryHilbertCarrier_parallelogram
    (y - z) z
  abel_nf at *
  linear_combination (-h1 + h2 + h3 - h4) / 8

/-- Symmetry upgrades left additivity to additivity in the second argument. -/
theorem auxiliaryPolarization_add_right
    (A : XBallTheoryModel.{u})
    (x y z : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryPolarization x (y + z) =
      A.auxiliaryPolarization x y + A.auxiliaryPolarization x z := by
  rw [A.auxiliaryPolarization_comm,
    A.auxiliaryPolarization_add_left,
    A.auxiliaryPolarization_comm y x,
    A.auxiliaryPolarization_comm z x]

theorem auxiliaryPolarization_sub_left
    (A : XBallTheoryModel.{u})
    (x y z : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryPolarization (x - y) z =
      A.auxiliaryPolarization x z - A.auxiliaryPolarization y z := by
  rw [sub_eq_add_neg, A.auxiliaryPolarization_add_left,
    A.auxiliaryPolarization_neg_left, sub_eq_add_neg]

theorem auxiliaryPolarization_sub_right
    (A : XBallTheoryModel.{u})
    (x y z : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryPolarization x (y - z) =
      A.auxiliaryPolarization x y - A.auxiliaryPolarization x z := by
  rw [sub_eq_add_neg, A.auxiliaryPolarization_add_right,
    A.auxiliaryPolarization_neg_right, sub_eq_add_neg]

/-- Polarization against a fixed second argument as an additive homomorphism. -/
noncomputable def auxiliaryPolarizationAddHomLeft
    (A : XBallTheoryModel.{u}) (y : A.AuxiliaryHilbertCarrier) :
    A.AuxiliaryHilbertCarrier →+ ℝ where
  toFun x := A.auxiliaryPolarization x y
  map_zero' := A.auxiliaryPolarization_zero_left y
  map_add' x z := A.auxiliaryPolarization_add_left x z y

@[simp] theorem auxiliaryPolarizationAddHomLeft_apply
    (A : XBallTheoryModel.{u}) (x y : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryPolarizationAddHomLeft y x =
      A.auxiliaryPolarization x y :=
  rfl

/-- Polarization against a fixed first argument as an additive homomorphism. -/
noncomputable def auxiliaryPolarizationAddHomRight
    (A : XBallTheoryModel.{u}) (x : A.AuxiliaryHilbertCarrier) :
    A.AuxiliaryHilbertCarrier →+ ℝ where
  toFun y := A.auxiliaryPolarization x y
  map_zero' := A.auxiliaryPolarization_zero_right x
  map_add' y z := A.auxiliaryPolarization_add_right x y z

@[simp] theorem auxiliaryPolarizationAddHomRight_apply
    (A : XBallTheoryModel.{u}) (x y : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryPolarizationAddHomRight x y =
      A.auxiliaryPolarization x y :=
  rfl

/-- Every additive map between rational vector spaces is rational-linear;
applied to polarization this gives scalar homogeneity on the dense rational
subfield of `ℝ`. -/
theorem auxiliaryPolarization_rat_smul_left
    (A : XBallTheoryModel.{u}) (q : ℚ)
    (x y : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryPolarization ((q : ℝ) • x) y =
      (q : ℝ) * A.auxiliaryPolarization x y := by
  simpa [smul_eq_mul] using
    map_ratCast_smul (A.auxiliaryPolarizationAddHomLeft y)
      ℝ ℝ q x

theorem auxiliaryPolarization_rat_smul_right
    (A : XBallTheoryModel.{u}) (q : ℚ)
    (x y : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryPolarization x ((q : ℝ) • y) =
      (q : ℝ) * A.auxiliaryPolarization x y := by
  rw [A.auxiliaryPolarization_comm,
    A.auxiliaryPolarization_rat_smul_left,
    A.auxiliaryPolarization_comm]

/-- Polarization expressed entirely on the original completed Banach carrier.
This is the bridge used to inherit continuity before the auxiliary triangle
inequality has been constructed. -/
theorem auxiliaryPolarization_eq_completed
    (A : XBallTheoryModel.{u})
    (x y : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryPolarization x y =
      (A.completedHilbertValue
          (A.auxiliaryHilbertCarrierEquiv x +
            A.auxiliaryHilbertCarrierEquiv y) ^ 2 -
        A.completedHilbertValue
          (A.auxiliaryHilbertCarrierEquiv x -
            A.auxiliaryHilbertCarrierEquiv y) ^ 2) / 4 := by
  unfold auxiliaryPolarization
  rw [A.norm_auxiliaryHilbertCarrier,
    A.norm_auxiliaryHilbertCarrier]
  change
    (A.completedHilbertValue
          (A.auxiliaryHilbertCarrierEquiv (x + y)) ^ 2 -
        A.completedHilbertValue
          (A.auxiliaryHilbertCarrierEquiv (x - y)) ^ 2) / 4 = _
  rw [
    show A.auxiliaryHilbertCarrierEquiv (x + y) =
      A.auxiliaryHilbertCarrierEquiv x +
        A.auxiliaryHilbertCarrierEquiv y by
      exact A.auxiliaryHilbertCarrierAddEquiv.map_add x y,
    show A.auxiliaryHilbertCarrierEquiv (x - y) =
      A.auxiliaryHilbertCarrierEquiv x -
        A.auxiliaryHilbertCarrierEquiv y by
      exact A.auxiliaryHilbertCarrierAddEquiv.map_sub x y]

/-- Scalarized polarization is continuous in the real scalar, measured via
the already constructed Banach topology on the original carrier. -/
theorem continuous_auxiliaryPolarization_smul_left
    (A : XBallTheoryModel.{u})
    (x y : A.AuxiliaryHilbertCarrier) :
    Continuous (fun r : ℝ ↦ A.auxiliaryPolarization (r • x) y) := by
  rw [show (fun r : ℝ ↦ A.auxiliaryPolarization (r • x) y) =
      fun r : ℝ ↦
        (A.completedHilbertValue
            (r • A.auxiliaryHilbertCarrierEquiv x +
              A.auxiliaryHilbertCarrierEquiv y) ^ 2 -
          A.completedHilbertValue
            (r • A.auxiliaryHilbertCarrierEquiv x -
              A.auxiliaryHilbertCarrierEquiv y) ^ 2) / 4 by
    funext r
    rw [A.auxiliaryPolarization_eq_completed,
      show A.auxiliaryHilbertCarrierEquiv (r • x) =
        r • A.auxiliaryHilbertCarrierEquiv x by
        exact A.auxiliaryHilbertCarrierLinearEquiv.map_smul r x]]
  have hsmul : Continuous
      (fun r : ℝ ↦ r • A.auxiliaryHilbertCarrierEquiv x) :=
    (A.realSmul_uniformContinuous_fixed
      (A.auxiliaryHilbertCarrierEquiv x)).continuous
  exact ((((A.completedHilbertValue_uniformContinuous.continuous.comp
      (hsmul.add continuous_const)).pow 2).sub
        ((A.completedHilbertValue_uniformContinuous.continuous.comp
          (hsmul.sub continuous_const)).pow 2)).div_const 4)

/-- Rational homogeneity extends to every real scalar by continuity and
density of the rational subfield. -/
theorem auxiliaryPolarization_smul_left
    (A : XBallTheoryModel.{u}) (r : ℝ)
    (x y : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryPolarization (r • x) y =
      r * A.auxiliaryPolarization x y := by
  refine Rat.denseRange_cast.induction_on r
    (isClosed_eq
      (A.continuous_auxiliaryPolarization_smul_left x y)
      (continuous_id.mul continuous_const)) ?_
  intro q
  exact A.auxiliaryPolarization_rat_smul_left q x y

theorem auxiliaryPolarization_smul_right
    (A : XBallTheoryModel.{u}) (r : ℝ)
    (x y : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryPolarization x (r • y) =
      r * A.auxiliaryPolarization x y := by
  rw [A.auxiliaryPolarization_comm,
    A.auxiliaryPolarization_smul_left,
    A.auxiliaryPolarization_comm]

/-- Polarization against a fixed vector is now a genuine real-linear map. -/
noncomputable def auxiliaryPolarizationLinearMapLeft
    (A : XBallTheoryModel.{u}) (y : A.AuxiliaryHilbertCarrier) :
    A.AuxiliaryHilbertCarrier →ₗ[ℝ] ℝ where
  toFun x := A.auxiliaryPolarization x y
  map_add' x z := A.auxiliaryPolarization_add_left x z y
  map_smul' r x := by
    simpa [smul_eq_mul] using
      A.auxiliaryPolarization_smul_left r x y

@[simp] theorem auxiliaryPolarizationLinearMapLeft_apply
    (A : XBallTheoryModel.{u}) (x y : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryPolarizationLinearMapLeft y x =
      A.auxiliaryPolarization x y :=
  rfl

/-- The reconstructed polarization satisfies exactly the algebraic and
positivity axioms from which Mathlib derives an inner-product norm and its
triangle inequality. -/
@[implicit_reducible]
noncomputable def auxiliaryInnerProductCore
    (A : XBallTheoryModel.{u}) :
    InnerProductSpace.Core ℝ A.AuxiliaryHilbertCarrier where
  inner := A.auxiliaryPolarization
  conj_inner_symm x y := by
    simpa using A.auxiliaryPolarization_comm y x
  re_inner_nonneg x := by
    simpa using A.auxiliaryPolarization_self_nonneg x
  add_left x y z := A.auxiliaryPolarization_add_left x y z
  smul_left x y r := by
    simpa using A.auxiliaryPolarization_smul_left r x y
  definite x hx :=
    (A.auxiliaryPolarization_self_eq_zero_iff x).1 hx

/-- The norm generated abstractly by the inner-product core is exactly the
already installed auxiliary norm operation. -/
theorem sqrt_auxiliaryPolarization_self
    (A : XBallTheoryModel.{u})
    (x : A.AuxiliaryHilbertCarrier) :
    Real.sqrt (A.auxiliaryPolarization x x) = ‖x‖ := by
  rw [A.auxiliaryPolarization_self,
    Real.sqrt_sq (A.norm_auxiliaryHilbertCarrier_nonneg x)]

/-- Cauchy--Schwarz for the reconstructed polarization, expressed using the
existing auxiliary norm operation. -/
theorem auxiliaryPolarization_le_norm_mul_norm
    (A : XBallTheoryModel.{u})
    (x y : A.AuxiliaryHilbertCarrier) :
    A.auxiliaryPolarization x y ≤ ‖x‖ * ‖y‖ := by
  letI : InnerProductSpace.Core ℝ A.AuxiliaryHilbertCarrier :=
    A.auxiliaryInnerProductCore
  have h := InnerProductSpace.Core.inner_mul_inner_self_le
    (𝕜 := ℝ) x y
  have hsq :
      |A.auxiliaryPolarization x y| *
          |A.auxiliaryPolarization x y| ≤
        (‖x‖ * ‖y‖) * (‖x‖ * ‖y‖) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    change
      |A.auxiliaryPolarization x y| *
          |A.auxiliaryPolarization y x| ≤
        A.auxiliaryPolarization x x *
          A.auxiliaryPolarization y y at h
    rw [A.auxiliaryPolarization_comm y x,
      A.auxiliaryPolarization_self,
      A.auxiliaryPolarization_self] at h
    calc
      |A.auxiliaryPolarization x y| *
          |A.auxiliaryPolarization x y| ≤
          ‖x‖ ^ 2 * ‖y‖ ^ 2 := h
      _ = (‖x‖ * ‖y‖) * (‖x‖ * ‖y‖) := by ring
  exact (le_abs_self (A.auxiliaryPolarization x y)).trans
    (nonneg_le_nonneg_of_sq_le_sq
      (mul_nonneg
        (A.norm_auxiliaryHilbertCarrier_nonneg x)
        (A.norm_auxiliaryHilbertCarrier_nonneg y)) hsq)

/-- The missing triangle inequality for the auxiliary norm, derived from the
inner-product core's Cauchy--Schwarz theorem. -/
theorem norm_auxiliaryHilbertCarrier_triangle
    (A : XBallTheoryModel.{u})
    (x y : A.AuxiliaryHilbertCarrier) :
    ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq
    (add_nonneg
      (A.norm_auxiliaryHilbertCarrier_nonneg x)
      (A.norm_auxiliaryHilbertCarrier_nonneg y))
  calc
    ‖x + y‖ * ‖x + y‖ =
        A.auxiliaryPolarization (x + y) (x + y) := by
      rw [A.auxiliaryPolarization_self, pow_two]
    _ = A.auxiliaryPolarization x x +
          A.auxiliaryPolarization x y +
          A.auxiliaryPolarization y x +
          A.auxiliaryPolarization y y := by
      rw [A.auxiliaryPolarization_add_left,
        A.auxiliaryPolarization_add_right,
        A.auxiliaryPolarization_add_right]
      ring
    _ ≤ (‖x‖ + ‖y‖) * (‖x‖ + ‖y‖) := by
      rw [A.auxiliaryPolarization_self,
        A.auxiliaryPolarization_self,
        A.auxiliaryPolarization_comm y x]
      have hxy := A.auxiliaryPolarization_le_norm_mul_norm x y
      nlinarith

/-- The minimal normed-space axioms for the auxiliary norm. The triangle field
is the theorem derived above from the inner-product core. -/
@[implicit_reducible]
noncomputable def auxiliaryNormedSpaceCore
    (A : XBallTheoryModel.{u}) :
    NormedSpace.Core ℝ A.AuxiliaryHilbertCarrier where
  norm_nonneg := A.norm_auxiliaryHilbertCarrier_nonneg
  norm_smul := A.norm_auxiliaryHilbertCarrier_smul
  norm_triangle := A.norm_auxiliaryHilbertCarrier_triangle
  norm_eq_zero_iff := A.norm_auxiliaryHilbertCarrier_eq_zero_iff

/-- The reconstructed auxiliary norm is now a genuine normed additive-group
structure. -/
noncomputable instance (A : XBallTheoryModel.{u}) :
    NormedAddCommGroup A.AuxiliaryHilbertCarrier :=
  NormedAddCommGroup.ofCore A.auxiliaryNormedSpaceCore

/-- The transported real module and reconstructed auxiliary norm form a
normed real vector space. -/
noncomputable instance (A : XBallTheoryModel.{u}) :
    NormedSpace ℝ A.AuxiliaryHilbertCarrier :=
  NormedSpace.ofCore A.auxiliaryNormedSpaceCore

/-- The auxiliary polarization is the inner product inducing the reconstructed
auxiliary norm. -/
noncomputable instance (A : XBallTheoryModel.{u}) :
    InnerProductSpace ℝ A.AuxiliaryHilbertCarrier where
  inner := A.auxiliaryPolarization
  norm_sq_eq_re_inner x := by
    simp
  conj_inner_symm x y := by
    simpa using A.auxiliaryPolarization_comm y x
  add_left x y z := A.auxiliaryPolarization_add_left x y z
  smul_left x y r := by
    simpa using A.auxiliaryPolarization_smul_left r x y

/-- The auxiliary Hilbert norm and the original reconstructed Banach norm are
continuously linearly equivalent with the paper's exact constants. -/
noncomputable def auxiliaryHilbertContinuousLinearEquiv
    (A : XBallTheoryModel.{u}) :
    A.AuxiliaryHilbertCarrier ≃L[ℝ] A.CompletedDirectedPoint :=
  A.auxiliaryHilbertCarrierLinearEquiv.toContinuousLinearEquivOfBounds
    (Real.sqrt 3) 1
    (fun x ↦ A.original_norm_le_sqrtThree_mul_auxiliaryHilbertCarrier x)
    (fun x ↦ by
      have h := A.norm_auxiliaryHilbertCarrier_le_original
        (A.auxiliaryHilbertCarrierLinearEquiv.symm x)
      rw [one_mul]
      calc
        ‖A.auxiliaryHilbertCarrierLinearEquiv.symm x‖ ≤
            ‖AuxiliaryHilbertCarrier.toCompletedDirectedPoint
              (A.auxiliaryHilbertCarrierLinearEquiv.symm x)‖ := h
        _ = ‖x‖ := by
          congr 1)

/-- Completeness transfers from the original Banach completion through the
continuous linear equivalence. -/
noncomputable instance (A : XBallTheoryModel.{u}) :
    CompleteSpace A.AuxiliaryHilbertCarrier :=
  (completeSpace_congr
    A.auxiliaryHilbertContinuousLinearEquiv.isUniformEmbedding).mpr
      inferInstance

/-- Sortwise separability of the typed ball model also transfers to the
auxiliary Hilbert norm. -/
theorem auxiliaryHilbertCarrier_separableSpace
    (A : XBallTheoryModel.{u})
    (hseparable : ∀ radius : ℚ≥0,
      IsSeparable (Set.univ : Set (A.model.Ball radius))) :
    SeparableSpace A.AuxiliaryHilbertCarrier := by
  letI : SeparableSpace A.CompletedDirectedPoint :=
    A.completedDirectedPoint_separableSpace hseparable
  exact
    A.auxiliaryHilbertContinuousLinearEquiv.symm.surjective.denseRange.separableSpace
      A.auxiliaryHilbertContinuousLinearEquiv.symm.continuous

/-! ## Canonical maps from the typed ball sorts into the completion -/

/-- The canonical map from one rational-radius sort into the reconstructed
completed one-sorted carrier. -/
def ballToCompletedDirectedPoint (A : XBallTheoryModel.{u}) (radius : ℚ≥0) :
    A.model.Ball radius → A.CompletedDirectedPoint := fun x ↦
  A.toCompletedDirectedPoint
    (A.toSeparatedDirectedPoint ⟨radius, x⟩)

/-- The typed-sort metric and reconstructed metric differ by exactly the
language normalization used in the directed union. -/
theorem dist_ballToCompletedDirectedPoint
    (A : XBallTheoryModel.{u}) (radius : ℚ≥0)
    (x y : A.model.Ball radius) :
    dist (A.ballToCompletedDirectedPoint radius x)
        (A.ballToCompletedDirectedPoint radius y) =
      rationalBallMetricBound radius *
        (dist x y / A.model.sortBound radius) := by
  rw [ballToCompletedDirectedPoint, ballToCompletedDirectedPoint,
    A.dist_toCompletedDirectedPoint, A.dist_toSeparatedDirectedPoint,
    A.directedDistance_sameRadius]

/-- Radius inclusions do not change the reconstructed completed point. -/
theorem ballToCompletedDirectedPoint_inclusion
    (A : XBallTheoryModel.{u}) {r s : ℚ≥0} (h : r ≤ s)
    (x : A.model.Ball r) :
    A.ballToCompletedDirectedPoint s (A.model.inclusion h x) =
      A.ballToCompletedDirectedPoint r x := by
  unfold ballToCompletedDirectedPoint
  rw [A.toSeparatedDirectedPoint_inclusion]

/-- Every typed zero maps to the completed zero. -/
@[simp] theorem ballToCompletedDirectedPoint_zero
    (A : XBallTheoryModel.{u}) (radius : ℚ≥0) :
    A.ballToCompletedDirectedPoint radius (A.model.zero radius) = 0 := by
  unfold ballToCompletedDirectedPoint
  rw [A.toSeparatedDirectedPoint_zero]
  exact UniformSpace.Completion.coe_zero

/-- Every point from the radius-`r` sort lands in the reconstructed closed
ball of metric radius `rationalBallMetricBound r`. -/
theorem dist_ballToCompletedDirectedPoint_zero_le
    (A : XBallTheoryModel.{u}) (radius : ℚ≥0)
    (x : A.model.Ball radius) :
    dist (A.ballToCompletedDirectedPoint radius x) 0 ≤
      rationalBallMetricBound radius := by
  rw [← A.ballToCompletedDirectedPoint_zero radius,
    A.dist_ballToCompletedDirectedPoint]
  calc
    rationalBallMetricBound radius *
        (dist x (A.model.zero radius) / A.model.sortBound radius) ≤
      rationalBallMetricBound radius * 1 :=
        mul_le_mul_of_nonneg_left
          ((div_le_one (A.model.sortBound_pos radius)).2
            (A.model.dist_le_sortBound radius x (A.model.zero radius)))
          (rationalBallMetricBound_pos radius).le
    _ = rationalBallMetricBound radius := mul_one _

/-- The canonical typed-sort maps preserve negation. -/
@[simp] theorem ballToCompletedDirectedPoint_neg
    (A : XBallTheoryModel.{u}) (radius : ℚ≥0)
    (x : A.model.Ball radius) :
    A.ballToCompletedDirectedPoint radius (A.model.neg radius x) =
      -A.ballToCompletedDirectedPoint radius x := by
  unfold ballToCompletedDirectedPoint
  change A.toCompletedDirectedPoint
      (A.toSeparatedDirectedPoint (A.directedNeg ⟨radius, x⟩)) =
    -A.toCompletedDirectedPoint (A.toSeparatedDirectedPoint ⟨radius, x⟩)
  rw [← A.separatedNeg_toSeparatedDirectedPoint]
  exact UniformSpace.Completion.coe_neg
    (A.toSeparatedDirectedPoint ⟨radius, x⟩)

/-- The canonical typed-sort maps preserve binary addition, including its
exact output radius. -/
@[simp] theorem ballToCompletedDirectedPoint_add
    (A : XBallTheoryModel.{u}) (r s : ℚ≥0)
    (x : A.model.Ball r) (y : A.model.Ball s) :
    A.ballToCompletedDirectedPoint (r + s) (A.model.add r s (x, y)) =
      A.ballToCompletedDirectedPoint r x +
        A.ballToCompletedDirectedPoint s y := by
  unfold ballToCompletedDirectedPoint
  change A.toCompletedDirectedPoint
      (A.toSeparatedDirectedPoint (A.directedAdd ⟨r, x⟩ ⟨s, y⟩)) =
    A.toCompletedDirectedPoint (A.toSeparatedDirectedPoint ⟨r, x⟩) +
      A.toCompletedDirectedPoint (A.toSeparatedDirectedPoint ⟨s, y⟩)
  rw [← A.separatedAdd_toSeparatedDirectedPoint]
  exact UniformSpace.Completion.coe_add
    (A.toSeparatedDirectedPoint ⟨r, x⟩)
    (A.toSeparatedDirectedPoint ⟨s, y⟩)

/-- The canonical typed-sort maps preserve every rational scalar action and
its exact output radius. -/
@[simp] theorem ballToCompletedDirectedPoint_smul
    (A : XBallTheoryModel.{u}) (q : ℚ) (radius : ℚ≥0)
    (x : A.model.Ball radius) :
    A.ballToCompletedDirectedPoint (q.nnabs * radius)
        (A.model.smul q radius x) =
      q • A.ballToCompletedDirectedPoint radius x := by
  unfold ballToCompletedDirectedPoint
  change A.toCompletedDirectedPoint
      (A.toSeparatedDirectedPoint (A.directedSmul q ⟨radius, x⟩)) =
    q • A.toCompletedDirectedPoint
      (A.toSeparatedDirectedPoint ⟨radius, x⟩)
  rw [← A.separatedSmul_toSeparatedDirectedPoint]
  exact UniformSpace.Completion.coe_smul q
    (A.toSeparatedDirectedPoint ⟨radius, x⟩)

end XBallTheoryModel

end

end NormFormula.X.BallLanguage
