import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import NormFormula.ContinuousLogic.Ultralimit

/-!
# A bounded metric reduced product

This file constructs the metric carriers needed for a concrete continuous
compactness argument.  For a bounded pseudometric sort, sequences are given
the normalized ultralimit pseudometric.  Quotienting by distance zero then
produces an honest metric space.  A uniformly continuous `[0,1]`-valued
predicate descends to the two quotient sorts.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Filter
open scoped Topology

attribute [local instance] Structure.rowPseudoMetricSpace
  Structure.parameterPseudoMetricSpace Structure.rowNonempty
  Structure.parameterNonempty

universe u v

/-- A positive scale bounding all distances on one sort. -/
structure BoundedMetricSort (α : Type u) [PseudoMetricSpace α] where
  scale : ℝ
  scale_pos : 0 < scale
  dist_le_scale : ∀ x y : α, dist x y ≤ scale

namespace BoundedMetricSort

variable {α : Type u} [PseudoMetricSpace α]

/-- Distance normalized into the truth-value interval. -/
def normalizedDistance (B : BoundedMetricSort α) (x y : α) : TruthValue :=
  ⟨dist x y / B.scale,
    div_nonneg dist_nonneg B.scale_pos.le,
    (div_le_one B.scale_pos).2 (B.dist_le_scale x y)⟩

@[simp]
theorem coe_normalizedDistance (B : BoundedMetricSort α) (x y : α) :
    (B.normalizedDistance x y : ℝ) = dist x y / B.scale :=
  rfl

@[simp]
theorem normalizedDistance_self (B : BoundedMetricSort α) (x : α) :
    B.normalizedDistance x x =
      (⟨0, le_rfl, zero_le_one⟩ : TruthValue) := by
  ext
  simp [normalizedDistance]

theorem normalizedDistance_comm (B : BoundedMetricSort α) (x y : α) :
    B.normalizedDistance x y = B.normalizedDistance y x := by
  ext
  simp [dist_comm]

end BoundedMetricSort

/-- The sequence representatives for a reduced product of one bounded sort.
This is a type synonym so that it can carry the ultralimit pseudometric rather
than the usual supremum metric on function spaces. -/
def ReducedSequence {α : Type u} [PseudoMetricSpace α]
    (_B : BoundedMetricSort α) := ℕ → α

namespace ReducedSequence

variable {α : Type u} [PseudoMetricSpace α]
variable (B : BoundedMetricSort α)

instance [Nonempty α] : Nonempty (ReducedSequence B) :=
  inferInstanceAs (Nonempty (ℕ → α))

/-- The normalized ultralimit distance between two sequence representatives. -/
def sequenceDist (x y : ReducedSequence B) : ℝ :=
  (ultralimit fun n ↦ B.normalizedDistance (x n) (y n) : ℝ)

theorem sequenceDist_nonneg (x y : ReducedSequence B) :
    0 ≤ sequenceDist B x y :=
  (ultralimit fun n ↦ B.normalizedDistance (x n) (y n)).property.1

@[simp]
theorem sequenceDist_self (x : ReducedSequence B) :
    sequenceDist B x x = 0 := by
  unfold sequenceDist
  rw [show (fun n ↦ B.normalizedDistance (x n) (x n)) =
      (fun _ : ℕ ↦ (⟨0, le_rfl, zero_le_one⟩ : TruthValue)) by
    funext n
    exact B.normalizedDistance_self (x n)]
  simp

theorem sequenceDist_comm (x y : ReducedSequence B) :
    sequenceDist B x y = sequenceDist B y x := by
  unfold sequenceDist
  rw [show (fun n ↦ B.normalizedDistance (x n) (y n)) =
      (fun n ↦ B.normalizedDistance (y n) (x n)) by
    funext n
    exact B.normalizedDistance_comm (x n) (y n)]

theorem sequenceDist_triangle (x y z : ReducedSequence B) :
    sequenceDist B x z ≤ sequenceDist B x y + sequenceDist B y z := by
  apply ultralimit_coe_le_add_of_eventually_le
  filter_upwards [] with n
  simp only [BoundedMetricSort.coe_normalizedDistance]
  rw [← add_div]
  exact div_le_div_of_nonneg_right (dist_triangle (x n) (y n) (z n)) B.scale_pos.le

/-- The sequence space equipped with its normalized ultralimit pseudometric. -/
instance pseudoMetricSpace : PseudoMetricSpace (ReducedSequence B) where
  dist := sequenceDist B
  dist_self := sequenceDist_self B
  dist_comm := sequenceDist_comm B
  dist_triangle := sequenceDist_triangle B

@[simp]
theorem dist_eq_sequenceDist (x y : ReducedSequence B) :
    dist x y = sequenceDist B x y :=
  rfl

/-- Normalized coordinate distances converge to the reduced sequence
distance. -/
theorem tendsto_normalizedDistance (x y : ReducedSequence B) :
    Tendsto (fun n ↦ (B.normalizedDistance (x n) (y n) : ℝ))
      indexUltrafilter (𝓝 (sequenceDist B x y)) := by
  change Tendsto
    (fun n ↦ (B.normalizedDistance (x n) (y n) : ℝ))
    indexUltrafilter
    (𝓝 (ultralimit fun n ↦ B.normalizedDistance (x n) (y n) : ℝ))
  exact continuous_subtype_val.continuousAt.tendsto.comp
    (tendsto_ultralimit fun n ↦ B.normalizedDistance (x n) (y n))

end ReducedSequence

/-- The metric reduced product of a bounded pseudometric sort. -/
abbrev ReducedProduct {α : Type u} [PseudoMetricSpace α]
    (B : BoundedMetricSort α) :=
  SeparationQuotient (ReducedSequence B)

namespace ReducedProduct

variable {α : Type u} [PseudoMetricSpace α]
variable (B : BoundedMetricSort α)

/-- Send a sequence representative to its distance-zero equivalence class. -/
def mk (x : ReducedSequence B) : ReducedProduct B :=
  SeparationQuotient.mk x

/-- The diagonal embedding by a constant sequence. -/
def const (x : α) : ReducedProduct B :=
  mk B (fun _ ↦ x)

@[simp]
theorem dist_mk (x y : ReducedSequence B) :
    dist (mk B x) (mk B y) = ReducedSequence.sequenceDist B x y := by
  exact SeparationQuotient.dist_mk x y

@[simp]
theorem dist_const (x y : α) :
    dist (const B x) (const B y) = dist x y / B.scale := by
  rw [show const B x = SeparationQuotient.mk
      (show ReducedSequence B from fun _ : ℕ ↦ x) by rfl,
    show const B y = SeparationQuotient.mk
      (show ReducedSequence B from fun _ : ℕ ↦ y) by rfl,
    SeparationQuotient.dist_mk]
  change ReducedSequence.sequenceDist B (fun _ ↦ x) (fun _ ↦ y) = _
  unfold ReducedSequence.sequenceDist
  rw [show (fun _ : ℕ ↦ B.normalizedDistance x y) =
      (fun _ : ℕ ↦ B.normalizedDistance x y) by rfl,
    ultralimit_const]
  rfl

end ReducedProduct

/-- Uniformly continuous maps carry pairs whose mutual distance tends to zero
to pairs with the same property. -/
theorem tendsto_dist_zero_of_uniformContinuous
    {ι A C : Type*} [PseudoMetricSpace A] [PseudoMetricSpace C]
    {l : Filter ι} {f : A → C} (hf : UniformContinuous f)
    {x y : ι → A}
    (hxy : Tendsto (fun i ↦ dist (x i) (y i)) l (𝓝 0)) :
    Tendsto (fun i ↦ dist (f (x i)) (f (y i))) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hmodulus⟩ := Metric.uniformContinuous_iff.1 hf ε hε
  filter_upwards [(Metric.tendsto_nhds.1 hxy δ hδ)] with i hi
  have hi' : dist (x i) (y i) < δ := by
    simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using hi
  have hout := hmodulus hi'
  simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using hout

namespace ReducedSequence

variable {α : Type u} [PseudoMetricSpace α]
variable (B : BoundedMetricSort α)

/-- If two representatives have reduced distance zero, then their original
coordinate distances tend to zero along the ultrafilter. -/
theorem tendsto_coordinateDist_zero {x y : ReducedSequence B}
    (hxy : dist x y = 0) :
    Tendsto (fun n ↦ dist (x n) (y n)) indexUltrafilter (𝓝 0) := by
  have hnormalized : Tendsto
      (fun n ↦ (B.normalizedDistance (x n) (y n) : ℝ))
      indexUltrafilter (𝓝 0) := by
    have h := continuous_subtype_val.continuousAt.tendsto.comp
      (tendsto_ultralimit fun n ↦ B.normalizedDistance (x n) (y n))
    have hseq : sequenceDist B x y = 0 := hxy
    change Tendsto (fun n ↦ (B.normalizedDistance (x n) (y n) : ℝ))
      indexUltrafilter (𝓝 (sequenceDist B x y)) at h
    rw [hseq] at h
    exact h
  have hscaled : Tendsto
      (fun n ↦ B.scale * (B.normalizedDistance (x n) (y n) : ℝ))
      indexUltrafilter (𝓝 (B.scale * 0)) :=
    tendsto_const_nhds.mul hnormalized
  convert hscaled using 1
  · funext n
    simp only [BoundedMetricSort.coe_normalizedDistance]
    symm
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ B.scale_pos.ne']
  · simp

end ReducedSequence

namespace Structure

/-- Bounded scales for both metric sorts of a continuous structure. -/
structure Bounds (M : Structure.{u, v}) where
  row : BoundedMetricSort M.Row
  parameter : BoundedMetricSort M.Parameter

end Structure

variable (M : Structure.{u, v}) (bounds : M.Bounds)

/-- Interpret the predicate coordinatewise and take its truth-value
ultralimit, before quotienting the two sequence sorts. -/
def reducedPredicateOnSequences
    (x : ReducedSequence bounds.row)
    (y : ReducedSequence bounds.parameter) : TruthValue :=
  ultralimit fun n ↦ M.predicate (x n) (y n)

/-- The ultralimit predicate is uniformly continuous on the two sequence
sorts.  Its modulus is inherited from the original predicate after accounting
for the two normalization scales. -/
theorem reducedPredicateOnSequences_uniformContinuous :
    UniformContinuous
      (fun p : ReducedSequence bounds.row × ReducedSequence bounds.parameter ↦
        reducedPredicateOnSequences M bounds p.1 p.2) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨η, hη, hmodulus⟩ := Metric.uniformContinuous_iff.1
    M.predicate_uniformContinuous (ε / 2) (half_pos hε)
  let δ := min (η / bounds.row.scale) (η / bounds.parameter.scale)
  have hδ : 0 < δ := lt_min
    (div_pos hη bounds.row.scale_pos)
    (div_pos hη bounds.parameter.scale_pos)
  refine ⟨δ, hδ, ?_⟩
  rintro a b hab
  have hab' : max (dist a.1 b.1) (dist a.2 b.2) < δ := by
    simpa only [Prod.dist_eq] using hab
  have hrow : ReducedSequence.sequenceDist bounds.row a.1 b.1 <
      η / bounds.row.scale := by
    exact (lt_of_le_of_lt (le_max_left _ _) hab').trans_le (min_le_left _ _)
  have hparameter : ReducedSequence.sequenceDist bounds.parameter a.2 b.2 <
      η / bounds.parameter.scale := by
    exact (lt_of_le_of_lt (le_max_right _ _) hab').trans_le (min_le_right _ _)
  have hrowEventually : ∀ᶠ n in indexUltrafilter,
      dist (a.1 n) (b.1 n) < η := by
    have hnormalized :=
      (ReducedSequence.tendsto_normalizedDistance bounds.row a.1 b.1).eventually_lt_const hrow
    filter_upwards [hnormalized] with n hn
    exact (div_lt_div_iff_of_pos_right bounds.row.scale_pos).1 hn
  have hparameterEventually : ∀ᶠ n in indexUltrafilter,
      dist (a.2 n) (b.2 n) < η := by
    have hnormalized :=
      (ReducedSequence.tendsto_normalizedDistance bounds.parameter a.2 b.2).eventually_lt_const
        hparameter
    filter_upwards [hnormalized] with n hn
    exact (div_lt_div_iff_of_pos_right bounds.parameter.scale_pos).1 hn
  have houtputEventually : ∀ᶠ n in indexUltrafilter,
      dist (M.predicate (a.1 n) (a.2 n))
        (M.predicate (b.1 n) (b.2 n)) ≤ ε / 2 := by
    filter_upwards [hrowEventually, hparameterEventually] with n hnrow hnparameter
    have hinput : dist (a.1 n, a.2 n) (b.1 n, b.2 n) < η := by
      rw [Prod.dist_eq]
      exact max_lt hnrow hnparameter
    exact (hmodulus hinput).le
  have houtputLimit : Tendsto
      (fun n ↦ dist (M.predicate (a.1 n) (a.2 n))
        (M.predicate (b.1 n) (b.2 n)))
      indexUltrafilter
      (𝓝 (dist (reducedPredicateOnSequences M bounds a.1 a.2)
        (reducedPredicateOnSequences M bounds b.1 b.2))) :=
    (tendsto_ultralimit fun n ↦ M.predicate (a.1 n) (a.2 n)).dist
      (tendsto_ultralimit fun n ↦ M.predicate (b.1 n) (b.2 n))
  exact (isClosed_Iic.mem_of_tendsto houtputLimit houtputEventually).trans_lt
    (half_lt_self hε)

/-- The sequence predicate only depends on the distance-zero classes of both
representatives. -/
theorem reducedPredicateOnSequences_eq_of_inseparable
    {x x' : ReducedSequence bounds.row}
    {y y' : ReducedSequence bounds.parameter}
    (hx : Inseparable x x') (hy : Inseparable y y') :
    reducedPredicateOnSequences M bounds x y =
      reducedPredicateOnSequences M bounds x' y' := by
  have hx0 := ReducedSequence.tendsto_coordinateDist_zero bounds.row
    (Metric.inseparable_iff.1 hx)
  have hy0 := ReducedSequence.tendsto_coordinateDist_zero bounds.parameter
    (Metric.inseparable_iff.1 hy)
  have hpair : Tendsto
      (fun n ↦ dist (x n, y n) (x' n, y' n))
      indexUltrafilter (𝓝 0) := by
    simpa [Prod.dist_eq] using hx0.max hy0
  have hout := tendsto_dist_zero_of_uniformContinuous
    M.predicate_uniformContinuous hpair
  have hultra : Tendsto
      (fun n ↦ dist (M.predicate (x n) (y n))
        (M.predicate (x' n) (y' n)))
      indexUltrafilter
      (𝓝 (dist (reducedPredicateOnSequences M bounds x y)
        (reducedPredicateOnSequences M bounds x' y'))) :=
    (tendsto_ultralimit fun n ↦ M.predicate (x n) (y n)).dist
      (tendsto_ultralimit fun n ↦ M.predicate (x' n) (y' n))
  exact dist_eq_zero.1 (tendsto_nhds_unique hultra hout)

/-- The predicate descended to the two metric separation quotients. -/
def reducedPredicate :
    ReducedProduct bounds.row → ReducedProduct bounds.parameter → TruthValue :=
  SeparationQuotient.lift₂ (reducedPredicateOnSequences M bounds) <| by
    intro x y x' y' hx hy
    exact reducedPredicateOnSequences_eq_of_inseparable M bounds hx hy

@[simp]
theorem reducedPredicate_mk
    (x : ReducedSequence bounds.row)
    (y : ReducedSequence bounds.parameter) :
    reducedPredicate M bounds (ReducedProduct.mk bounds.row x)
      (ReducedProduct.mk bounds.parameter y) =
      reducedPredicateOnSequences M bounds x y :=
  rfl

set_option maxHeartbeats 400000 in
/-- Uniform continuity survives passage from representatives to the metric
separation quotients because the quotient maps preserve distance. -/
theorem reducedPredicate_uniformContinuous :
    UniformContinuous
      (fun p : ReducedProduct bounds.row × ReducedProduct bounds.parameter ↦
        reducedPredicate M bounds p.1 p.2) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨δ, hδ, hmodulus⟩ := Metric.uniformContinuous_iff.1
    (reducedPredicateOnSequences_uniformContinuous M bounds) ε hε
  refine ⟨δ, hδ, ?_⟩
  let q : ReducedSequence bounds.row × ReducedSequence bounds.parameter →
      ReducedProduct bounds.row × ReducedProduct bounds.parameter :=
    Prod.map SeparationQuotient.mk SeparationQuotient.mk
  have hq : Function.Surjective q :=
    SeparationQuotient.surjective_mk.prodMap SeparationQuotient.surjective_mk
  intro a b hab
  obtain ⟨a, rfl⟩ := hq a
  obtain ⟨b, rfl⟩ := hq b
  apply hmodulus
  simpa [q, Prod.dist_eq] using hab

/-- The bounded metric reduced product as an actual two-sorted continuous
structure. -/
def Structure.reducedProduct : Structure.{u, v} where
  Row := ReducedProduct bounds.row
  Parameter := ReducedProduct bounds.parameter
  rowPseudoMetricSpace := inferInstance
  parameterPseudoMetricSpace := inferInstance
  rowNonempty := inferInstance
  parameterNonempty := inferInstance
  predicate := reducedPredicate M bounds
  predicate_uniformContinuous := reducedPredicate_uniformContinuous M bounds

/-- The diagonal embedding preserves the distinguished predicate exactly. -/
@[simp]
theorem reducedProduct_predicate_const (x : M.Row) (y : M.Parameter) :
    (M.reducedProduct bounds).predicate
      (ReducedProduct.const bounds.row x)
      (ReducedProduct.const bounds.parameter y) = M.predicate x y := by
  change ultralimit (fun _ : ℕ ↦ M.predicate x y) = M.predicate x y
  exact ultralimit_const (M.predicate x y)

end


end NormFormula.ContinuousLogic
