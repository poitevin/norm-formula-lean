import Mathlib.Data.NNRat.Defs
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic.DeriveEncodable
import NormFormula.ModelTheory.LocalNIP

/-!
# Coherent rational-radius Banach balls

The standard many-sorted language for unbounded Banach spaces uses one
bounded sort for each radius.  This file defines the semantic operation layer
for a countable choice of radii, namely the nonnegative rationals.  It records
inclusions, zero, negation, addition, and multiplication by rational scalars,
together with the uniform continuity required of continuous-logic function
symbols.

This layer is intentionally independent of formula syntax.  The following
milestones can add typed terms and sentences while reusing the coherent
semantic target defined here.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open scoped Topology

universe u

deriving instance Encodable for NNRat

/-- A positive diameter bound for the rational-radius sort, including the
zero-radius ball. -/
def rationalBallMetricBound (r : ℚ≥0) : ℝ :=
  max 1 (2 * (r : ℝ))

theorem rationalBallMetricBound_pos (r : ℚ≥0) :
    0 < rationalBallMetricBound r :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

/-- The fixed language scale is monotone in the rational ball radius. -/
theorem rationalBallMetricBound_mono {r s : ℚ≥0} (h : r ≤ s) :
    rationalBallMetricBound r ≤ rationalBallMetricBound s := by
  unfold rationalBallMetricBound
  apply max_le_max le_rfl
  exact mul_le_mul_of_nonneg_left (NNRat.cast_mono h) (by norm_num)

/-- A countable rational-radius ball system carrying the standard Banach
operations.  The algebraic laws are imposed by the later theory; this
structure is the raw interpretation data for its function symbols. -/
structure RationalBallSystem where
  Ball : ℚ≥0 → Type u
  [ballPseudoMetricSpace : ∀ r, PseudoMetricSpace (Ball r)]
  [ballCompleteSpace : ∀ r, CompleteSpace (Ball r)]
  [ballNonempty : ∀ r, Nonempty (Ball r)]
  sortBound : ℚ≥0 → ℝ
  sortBound_pos : ∀ r, 0 < sortBound r
  dist_le_sortBound : ∀ (r) (x y : Ball r), dist x y ≤ sortBound r
  inclusion : ∀ {r s : ℚ≥0}, r ≤ s → Ball r → Ball s
  zero : ∀ r : ℚ≥0, Ball r
  neg : ∀ r : ℚ≥0, Ball r → Ball r
  add : ∀ r s : ℚ≥0, Ball r × Ball s → Ball (r + s)
  smul : ∀ (q : ℚ) (r : ℚ≥0), Ball r → Ball (q.nnabs * r)
  inclusion_uniformContinuous : ∀ {r s : ℚ≥0} (h : r ≤ s),
    UniformContinuous (inclusion h)
  neg_uniformContinuous : ∀ r : ℚ≥0, UniformContinuous (neg r)
  add_uniformContinuous : ∀ r s : ℚ≥0, UniformContinuous (add r s)
  smul_uniformContinuous : ∀ (q : ℚ) (r : ℚ≥0),
    UniformContinuous (smul q r)

attribute [instance] RationalBallSystem.ballPseudoMetricSpace
attribute [instance] RationalBallSystem.ballCompleteSpace
attribute [instance] RationalBallSystem.ballNonempty

/-- The closed ball of rational radius `r` in a real normed space. -/
abbrev RationalNormBall (E : Type*) [Norm E] (r : ℚ≥0) :=
  NormFormula.ClosedNormBall E (r : ℝ)

variable {E : Type*} [NormedAddCommGroup E]

/-- Every rational-radius closed ball in a Banach space is complete. -/
noncomputable instance rationalNormBallCompleteSpace [CompleteSpace E]
    (r : ℚ≥0) : CompleteSpace (RationalNormBall E r) :=
  (isClosed_le continuous_norm continuous_const).completeSpace_coe

/-- Coercion of a rational-radius inclusion. -/
def rationalBallInclusion {r s : ℚ≥0} (h : r ≤ s) :
    RationalNormBall E r → RationalNormBall E s :=
  fun x ↦ ⟨x.1, x.2.trans (NNRat.cast_mono h)⟩

/-- Zero belongs to every rational-radius ball. -/
def rationalBallZero (r : ℚ≥0) : RationalNormBall E r :=
  ⟨0, by simpa using (NNRat.cast_nonneg (α := ℝ) r)⟩

/-- Negation preserves every centered ball. -/
def rationalBallNeg (r : ℚ≥0) :
    RationalNormBall E r → RationalNormBall E r :=
  fun x ↦ ⟨-x.1, by simpa using x.2⟩

/-- Addition maps the product of the `r`- and `s`-balls into the
`r+s`-ball. -/
def rationalBallAdd (r s : ℚ≥0) :
    RationalNormBall E r × RationalNormBall E s →
      RationalNormBall E (r + s) :=
  fun p ↦ ⟨p.1.1 + p.2.1, by
    calc
      ‖p.1.1 + p.2.1‖ ≤ ‖p.1.1‖ + ‖p.2.1‖ := norm_add_le _ _
      _ ≤ (r : ℝ) + (s : ℝ) := add_le_add p.1.2 p.2.2
      _ = ((r + s : ℚ≥0) : ℝ) := by norm_cast⟩

/-- Rational scalar multiplication maps the `r`-ball into the ball of exact
radius `|q|r`. -/
def rationalBallSmul [NormedSpace ℝ E] (q : ℚ) (r : ℚ≥0) :
    RationalNormBall E r → RationalNormBall E (q.nnabs * r) :=
  fun x ↦ ⟨(q : ℝ) • x.1, by
    rw [norm_smul, Real.norm_eq_abs]
    have hq : |(q : ℝ)| = ((q.nnabs : ℚ≥0) : ℝ) := by
      norm_cast
    rw [hq]
    calc
      ((q.nnabs : ℚ≥0) : ℝ) * ‖x.1‖ ≤
          ((q.nnabs : ℚ≥0) : ℝ) * (r : ℝ) :=
        mul_le_mul_of_nonneg_left x.2 (by positivity)
      _ = ((q.nnabs * r : ℚ≥0) : ℝ) := by norm_cast⟩

/-- Rational-radius inclusions are uniformly continuous. -/
theorem rationalBallInclusion_uniformContinuous {r s : ℚ≥0} (h : r ≤ s) :
    UniformContinuous (rationalBallInclusion (E := E) h) :=
  uniformContinuous_subtype_val.subtype_mk _

/-- Negation on a rational-radius ball is uniformly continuous. -/
theorem rationalBallNeg_uniformContinuous (r : ℚ≥0) :
    UniformContinuous (rationalBallNeg (E := E) r) :=
  uniformContinuous_subtype_val.neg.subtype_mk _

/-- Addition between rational-radius balls is uniformly continuous. -/
theorem rationalBallAdd_uniformContinuous (r s : ℚ≥0) :
    UniformContinuous (rationalBallAdd (E := E) r s) := by
  have hfst : UniformContinuous
      (fun p : RationalNormBall E r × RationalNormBall E s ↦ p.1.1) :=
    uniformContinuous_subtype_val.comp uniformContinuous_fst
  have hsnd : UniformContinuous
      (fun p : RationalNormBall E r × RationalNormBall E s ↦ p.2.1) :=
    uniformContinuous_subtype_val.comp uniformContinuous_snd
  exact (hfst.add hsnd).subtype_mk _

/-- Rational scalar multiplication on a rational-radius ball is uniformly
continuous. -/
theorem rationalBallSmul_uniformContinuous [NormedSpace ℝ E]
    (q : ℚ) (r : ℚ≥0) :
    UniformContinuous (rationalBallSmul (E := E) q r) := by
  change UniformContinuous fun x : RationalNormBall E r ↦
    (⟨(q : ℝ) • x.1, _⟩ : RationalNormBall E (q.nnabs * r))
  exact (uniformContinuous_subtype_val.const_smul (q : ℝ)).subtype_mk _

/-- Every real normed space gives the standard coherent rational-radius ball
system. -/
def standardRationalBallSystem [NormedSpace ℝ E] [CompleteSpace E] :
    RationalBallSystem where
  Ball := RationalNormBall E
  ballPseudoMetricSpace := fun _ ↦ inferInstance
  ballCompleteSpace := fun _ ↦ inferInstance
  ballNonempty := fun r ↦ ⟨rationalBallZero (E := E) r⟩
  sortBound := rationalBallMetricBound
  sortBound_pos := rationalBallMetricBound_pos
  dist_le_sortBound := by
    intro r x y
    rw [Subtype.dist_eq, dist_eq_norm]
    calc
      ‖x.1 - y.1‖ ≤ ‖x.1‖ + ‖y.1‖ := norm_sub_le _ _
      _ ≤ (r : ℝ) + (r : ℝ) := add_le_add x.2 y.2
      _ = 2 * (r : ℝ) := by ring
      _ ≤ max 1 (2 * (r : ℝ)) := le_max_right _ _
  inclusion := rationalBallInclusion
  zero := rationalBallZero
  neg := rationalBallNeg
  add := rationalBallAdd
  smul := rationalBallSmul
  inclusion_uniformContinuous := rationalBallInclusion_uniformContinuous
  neg_uniformContinuous := rationalBallNeg_uniformContinuous
  add_uniformContinuous := rationalBallAdd_uniformContinuous
  smul_uniformContinuous := rationalBallSmul_uniformContinuous

/-- The metric diameter of the `r`-ball is bounded by the chosen positive
scale. -/
theorem rationalBall_dist_le_metricBound (r : ℚ≥0)
    (x y : RationalNormBall E r) :
    dist x y ≤ rationalBallMetricBound r := by
  rw [Subtype.dist_eq, dist_eq_norm]
  calc
    ‖x.1 - y.1‖ ≤ ‖x.1‖ + ‖y.1‖ := norm_sub_le _ _
    _ ≤ (r : ℝ) + (r : ℝ) := add_le_add x.2 y.2
    _ = 2 * (r : ℝ) := by ring
    _ ≤ max 1 (2 * (r : ℝ)) := le_max_right _ _

/-- Rational-radius balls cover the whole ambient normed space. -/
theorem exists_rationalNormBall (x : E) :
    ∃ r : ℚ≥0, ∃ y : RationalNormBall E r, (y : E) = x := by
  obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
  refine ⟨(n : ℚ≥0), ⟨x, ?_⟩, rfl⟩
  simpa using hn

@[simp]
theorem rationalBallInclusion_coe {r s : ℚ≥0} (h : r ≤ s)
    (x : RationalNormBall E r) :
    (rationalBallInclusion (E := E) h x : E) = x :=
  rfl

@[simp]
theorem rationalBallZero_coe (r : ℚ≥0) :
    (rationalBallZero (E := E) r : E) = 0 :=
  rfl

@[simp]
theorem rationalBallNeg_coe (r : ℚ≥0) (x : RationalNormBall E r) :
    (rationalBallNeg (E := E) r x : E) = -x :=
  rfl

@[simp]
theorem rationalBallAdd_coe (r s : ℚ≥0)
    (p : RationalNormBall E r × RationalNormBall E s) :
    (rationalBallAdd (E := E) r s p : E) = p.1.1 + p.2.1 :=
  rfl

@[simp]
theorem rationalBallSmul_coe [NormedSpace ℝ E] (q : ℚ) (r : ℚ≥0)
    (x : RationalNormBall E r) :
    (rationalBallSmul (E := E) q r x : E) = (q : ℝ) • x :=
  rfl

/-- Nested inclusions agree pointwise, the first coherence law needed by the
typed term semantics. -/
theorem rationalBallInclusion_trans {r s t : ℚ≥0}
    (hrs : r ≤ s) (hst : s ≤ t) (x : RationalNormBall E r) :
    rationalBallInclusion (E := E) hst
        (rationalBallInclusion (E := E) hrs x) =
      rationalBallInclusion (E := E) (hrs.trans hst) x := by
  rfl

/-- Inclusion commutes with negation. -/
theorem rationalBallInclusion_neg {r s : ℚ≥0} (h : r ≤ s)
    (x : RationalNormBall E r) :
    rationalBallInclusion (E := E) h (rationalBallNeg (E := E) r x) =
      rationalBallNeg (E := E) s (rationalBallInclusion (E := E) h x) := by
  rfl

/-- Inclusion commutes with addition. -/
theorem rationalBallInclusion_add {r r' s s' : ℚ≥0}
    (hr : r ≤ r') (hs : s ≤ s')
    (x : RationalNormBall E r) (y : RationalNormBall E s) :
    rationalBallInclusion (E := E) (add_le_add hr hs)
        (rationalBallAdd (E := E) r s (x, y)) =
      rationalBallAdd (E := E) r' s'
        (rationalBallInclusion (E := E) hr x,
          rationalBallInclusion (E := E) hs y) := by
  rfl

/-- Inclusion commutes with rational scalar multiplication. -/
theorem rationalBallInclusion_smul [NormedSpace ℝ E]
    {r s : ℚ≥0} (h : r ≤ s)
    (q : ℚ) (x : RationalNormBall E r) :
    rationalBallInclusion (E := E)
        (by gcongr)
        (rationalBallSmul (E := E) q r x) =
      rationalBallSmul (E := E) q s
        (rationalBallInclusion (E := E) h x) := by
  rfl

end

end NormFormula.ContinuousLogic
