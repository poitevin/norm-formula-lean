import NormFormula.ContinuousLogic.MultiReducedProduct
import NormFormula.ContinuousLogic.UltralimitAlong

/-!
# Bounded metric reduced products along an arbitrary ultrafilter

This is the index-polymorphic metric quotient underlying unrestricted
elementary-diagram compactness.  Both carrier metrics and every predicate are
taken along a supplied ultrafilter.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Filter
open scoped Topology

universe κ u v w

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.parameterPseudoMetricSpace MultiStructure.rowNonempty
  MultiStructure.parameterNonempty

/-- Families indexed by `ι`, equipped below with their normalized
ultrafilter pseudometric. -/
def ReducedSequenceAlong {ι : Type κ} (_U : Ultrafilter ι)
    {α : Type u} [PseudoMetricSpace α] (_B : BoundedMetricSort α) :=
  ι → α

namespace ReducedSequenceAlong

variable {ι : Type κ} (U : Ultrafilter ι)
  {α : Type u} [PseudoMetricSpace α] (B : BoundedMetricSort α)

instance [Nonempty α] : Nonempty (ReducedSequenceAlong U B) :=
  ⟨fun _ ↦ Classical.choice (inferInstance : Nonempty α)⟩

/-- Normalized ultralimit distance between two indexed representatives. -/
def sequenceDist (x y : ReducedSequenceAlong U B) : ℝ :=
  (ultralimitAlong U fun i ↦ B.normalizedDistance (x i) (y i) : ℝ)


@[simp]
theorem sequenceDist_self (x : ReducedSequenceAlong U B) :
    sequenceDist U B x x = 0 := by
  unfold sequenceDist
  rw [show (fun i ↦ B.normalizedDistance (x i) (x i)) =
      (fun _ : ι ↦ (⟨0, le_rfl, zero_le_one⟩ : TruthValue)) by
    funext i
    exact B.normalizedDistance_self (x i)]
  simp

theorem sequenceDist_comm (x y : ReducedSequenceAlong U B) :
    sequenceDist U B x y = sequenceDist U B y x := by
  unfold sequenceDist
  apply congrArg (fun value : TruthValue ↦ (value : ℝ))
  apply congrArg (ultralimitAlong U)
  funext i
  exact B.normalizedDistance_comm (x i) (y i)

theorem sequenceDist_triangle (x y z : ReducedSequenceAlong U B) :
    sequenceDist U B x z ≤ sequenceDist U B x y + sequenceDist U B y z := by
  apply ultralimitAlong_coe_le_add_of_eventually_le U
  filter_upwards [] with i
  simp only [BoundedMetricSort.coe_normalizedDistance]
  rw [← add_div]
  exact div_le_div_of_nonneg_right
    (dist_triangle (x i) (y i) (z i)) B.scale_pos.le

instance pseudoMetricSpace : PseudoMetricSpace (ReducedSequenceAlong U B) where
  dist := sequenceDist U B
  dist_self := sequenceDist_self U B
  dist_comm := sequenceDist_comm U B
  dist_triangle := sequenceDist_triangle U B


/-- Normalized coordinate distances converge to the reduced distance. -/
theorem tendsto_normalizedDistance (x y : ReducedSequenceAlong U B) :
    Tendsto (fun i ↦ (B.normalizedDistance (x i) (y i) : ℝ)) U
      (𝓝 (sequenceDist U B x y)) := by
  exact continuous_subtype_val.continuousAt.tendsto.comp
    (tendsto_ultralimitAlong U
      (fun i ↦ B.normalizedDistance (x i) (y i)))

/-- Distance-zero representatives have original coordinate distance tending
to zero along `U`. -/
theorem tendsto_coordinateDist_zero {x y : ReducedSequenceAlong U B}
    (hxy : dist x y = 0) :
    Tendsto (fun i ↦ dist (x i) (y i)) U (𝓝 0) := by
  have hnormalized : Tendsto
      (fun i ↦ (B.normalizedDistance (x i) (y i) : ℝ)) U (𝓝 0) := by
    have h := tendsto_normalizedDistance U B x y
    have hseq : sequenceDist U B x y = 0 := hxy
    rw [hseq] at h
    exact h
  have hscaled : Tendsto
      (fun i ↦ B.scale * (B.normalizedDistance (x i) (y i) : ℝ)) U
      (𝓝 (B.scale * 0)) :=
    tendsto_const_nhds.mul hnormalized
  convert hscaled using 1
  · funext i
    simp only [BoundedMetricSort.coe_normalizedDistance]
    symm
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ B.scale_pos.ne']
  · simp

end ReducedSequenceAlong

/-- Metric separation quotient of indexed representatives. -/
abbrev ReducedProductAlong {ι : Type κ} (U : Ultrafilter ι)
    {α : Type u} [PseudoMetricSpace α] (B : BoundedMetricSort α) :=
  SeparationQuotient (ReducedSequenceAlong U B)

namespace ReducedProductAlong

variable {ι : Type κ} (U : Ultrafilter ι)
  {α : Type u} [PseudoMetricSpace α] (B : BoundedMetricSort α)

/-- Quotient map from indexed representatives. -/
def mk (x : ReducedSequenceAlong U B) : ReducedProductAlong U B :=
  SeparationQuotient.mk x


end ReducedProductAlong

variable {ι : Type κ} (U : Ultrafilter ι)
  {Symbol : Type w} (M : MultiStructure.{u, v, w} Symbol)
  (bounds : M.Bounds)

/-- Coordinatewise interpretation of one symbol before quotienting. -/
def multiReducedPredicateOnSequencesAlong (symbol : Symbol)
    (x : ReducedSequenceAlong U bounds.row)
    (y : ReducedSequenceAlong U bounds.parameter) : TruthValue :=
  ultralimitAlong U fun i ↦ M.predicate symbol (x i) (y i)

/-- The prequotient predicate inherits uniform continuity. -/
theorem multiReducedPredicateOnSequencesAlong_uniformContinuous
    (symbol : Symbol) :
    UniformContinuous
      (fun p : ReducedSequenceAlong U bounds.row ×
          ReducedSequenceAlong U bounds.parameter ↦
        multiReducedPredicateOnSequencesAlong U M bounds symbol p.1 p.2) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨η, hη, hmodulus⟩ := Metric.uniformContinuous_iff.1
    (M.predicate_uniformContinuous symbol) (ε / 2) (half_pos hε)
  let δ := min (η / bounds.row.scale) (η / bounds.parameter.scale)
  have hδ : 0 < δ := lt_min
    (div_pos hη bounds.row.scale_pos)
    (div_pos hη bounds.parameter.scale_pos)
  refine ⟨δ, hδ, ?_⟩
  rintro a b hab
  have hab' : max (dist a.1 b.1) (dist a.2 b.2) < δ := by
    simpa only [Prod.dist_eq] using hab
  have hrow : ReducedSequenceAlong.sequenceDist U bounds.row a.1 b.1 <
      η / bounds.row.scale :=
    (lt_of_le_of_lt (le_max_left _ _) hab').trans_le (min_le_left _ _)
  have hparameter :
      ReducedSequenceAlong.sequenceDist U bounds.parameter a.2 b.2 <
        η / bounds.parameter.scale :=
    (lt_of_le_of_lt (le_max_right _ _) hab').trans_le (min_le_right _ _)
  have hrowEventually : ∀ᶠ i in U, dist (a.1 i) (b.1 i) < η := by
    have hnormalized :=
      (ReducedSequenceAlong.tendsto_normalizedDistance U bounds.row a.1 b.1)
        |>.eventually_lt_const hrow
    filter_upwards [hnormalized] with i hi
    exact (div_lt_div_iff_of_pos_right bounds.row.scale_pos).1 hi
  have hparameterEventually : ∀ᶠ i in U,
      dist (a.2 i) (b.2 i) < η := by
    have hnormalized :=
      (ReducedSequenceAlong.tendsto_normalizedDistance U bounds.parameter a.2 b.2)
        |>.eventually_lt_const hparameter
    filter_upwards [hnormalized] with i hi
    exact (div_lt_div_iff_of_pos_right bounds.parameter.scale_pos).1 hi
  have houtputEventually : ∀ᶠ i in U,
      dist (M.predicate symbol (a.1 i) (a.2 i))
        (M.predicate symbol (b.1 i) (b.2 i)) ≤ ε / 2 := by
    filter_upwards [hrowEventually, hparameterEventually] with i hr hp
    have hinput : dist (a.1 i, a.2 i) (b.1 i, b.2 i) < η := by
      rw [Prod.dist_eq]
      exact max_lt hr hp
    exact (hmodulus hinput).le
  have houtputLimit : Tendsto
      (fun i ↦ dist (M.predicate symbol (a.1 i) (a.2 i))
        (M.predicate symbol (b.1 i) (b.2 i))) U
      (𝓝 (dist
        (multiReducedPredicateOnSequencesAlong U M bounds symbol a.1 a.2)
        (multiReducedPredicateOnSequencesAlong U M bounds symbol b.1 b.2))) :=
    (tendsto_ultralimitAlong U
      (fun i ↦ M.predicate symbol (a.1 i) (a.2 i))).dist
    (tendsto_ultralimitAlong U
      (fun i ↦ M.predicate symbol (b.1 i) (b.2 i)))
  exact (isClosed_Iic.mem_of_tendsto houtputLimit houtputEventually).trans_lt
    (half_lt_self hε)

/-- The prequotient predicate depends only on distance-zero classes. -/
theorem multiReducedPredicateOnSequencesAlong_eq_of_inseparable
    (symbol : Symbol)
    {x x' : ReducedSequenceAlong U bounds.row}
    {y y' : ReducedSequenceAlong U bounds.parameter}
    (hx : Inseparable x x') (hy : Inseparable y y') :
    multiReducedPredicateOnSequencesAlong U M bounds symbol x y =
      multiReducedPredicateOnSequencesAlong U M bounds symbol x' y' := by
  have hx0 := ReducedSequenceAlong.tendsto_coordinateDist_zero U bounds.row
    (Metric.inseparable_iff.1 hx)
  have hy0 := ReducedSequenceAlong.tendsto_coordinateDist_zero U bounds.parameter
    (Metric.inseparable_iff.1 hy)
  have hpair : Tendsto (fun i ↦ dist (x i, y i) (x' i, y' i)) U (𝓝 0) := by
    simpa [Prod.dist_eq] using hx0.max hy0
  have hout := tendsto_dist_zero_of_uniformContinuous
    (M.predicate_uniformContinuous symbol) hpair
  have hultra : Tendsto
      (fun i ↦ dist (M.predicate symbol (x i) (y i))
        (M.predicate symbol (x' i) (y' i))) U
      (𝓝 (dist
        (multiReducedPredicateOnSequencesAlong U M bounds symbol x y)
        (multiReducedPredicateOnSequencesAlong U M bounds symbol x' y'))) :=
    (tendsto_ultralimitAlong U
      (fun i ↦ M.predicate symbol (x i) (y i))).dist
    (tendsto_ultralimitAlong U
      (fun i ↦ M.predicate symbol (x' i) (y' i)))
  exact dist_eq_zero.1 (tendsto_nhds_unique hultra hout)

/-- One symbol descended to the two metric separation quotients. -/
def multiReducedPredicateAlong (symbol : Symbol) :
    ReducedProductAlong U bounds.row →
      ReducedProductAlong U bounds.parameter → TruthValue :=
  SeparationQuotient.lift₂
    (multiReducedPredicateOnSequencesAlong U M bounds symbol) <| by
      intro x y x' y' hx hy
      exact multiReducedPredicateOnSequencesAlong_eq_of_inseparable
        U M bounds symbol hx hy

@[simp]
theorem multiReducedPredicateAlong_mk (symbol : Symbol)
    (x : ReducedSequenceAlong U bounds.row)
    (y : ReducedSequenceAlong U bounds.parameter) :
    multiReducedPredicateAlong U M bounds symbol
      (ReducedProductAlong.mk U bounds.row x)
      (ReducedProductAlong.mk U bounds.parameter y) =
      ultralimitAlong U (fun i ↦ M.predicate symbol (x i) (y i)) :=
  rfl

set_option maxHeartbeats 400000 in
/-- Uniform continuity descends to the metric quotient. -/
theorem multiReducedPredicateAlong_uniformContinuous (symbol : Symbol) :
    UniformContinuous
      (fun p : ReducedProductAlong U bounds.row ×
          ReducedProductAlong U bounds.parameter ↦
        multiReducedPredicateAlong U M bounds symbol p.1 p.2) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨δ, hδ, hmodulus⟩ := Metric.uniformContinuous_iff.1
    (multiReducedPredicateOnSequencesAlong_uniformContinuous U M bounds symbol)
      ε hε
  refine ⟨δ, hδ, ?_⟩
  let q : ReducedSequenceAlong U bounds.row ×
      ReducedSequenceAlong U bounds.parameter →
      ReducedProductAlong U bounds.row ×
        ReducedProductAlong U bounds.parameter :=
    Prod.map SeparationQuotient.mk SeparationQuotient.mk
  have hq : Function.Surjective q :=
    SeparationQuotient.surjective_mk.prodMap SeparationQuotient.surjective_mk
  intro a b hab
  obtain ⟨a, rfl⟩ := hq a
  obtain ⟨b, rfl⟩ := hq b
  apply hmodulus
  simpa [q, Prod.dist_eq] using hab

/-- The arbitrary-index many-predicate metric reduced product. -/
def MultiStructure.reducedProductAlong :
    MultiStructure.{max u κ, max v κ, w} Symbol where
  Row := ReducedProductAlong U bounds.row
  Parameter := ReducedProductAlong U bounds.parameter
  rowPseudoMetricSpace := inferInstance
  parameterPseudoMetricSpace := inferInstance
  rowNonempty := inferInstance
  parameterNonempty := inferInstance
  predicate := multiReducedPredicateAlong U M bounds
  predicate_uniformContinuous :=
    multiReducedPredicateAlong_uniformContinuous U M bounds

end

end NormFormula.ContinuousLogic
