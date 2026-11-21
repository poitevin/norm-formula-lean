import NormFormula.ContinuousLogic.ReducedProduct

/-!
# Uniformly continuous maps on bounded metric reduced products

This file supplies the functorial part of the bounded metric reduced-product
construction.  A uniformly continuous unary or binary map is interpreted
coordinatewise on sequence representatives.  The resulting map is uniformly
continuous for the normalized ultralimit pseudometrics, so it descends to the
metric separation quotients and still computes coordinatewise there.

The normalization scales of the source and target sorts need not agree.  The
proofs below explicitly rescale a modulus of uniform continuity; this is the
piece needed to lift the inclusions and Banach operations of a rational-ball
structure sort by sort.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Filter
open scoped Topology

universe u v w

namespace ReducedProduct

variable {A : Type u} {B : Type v} {C : Type w}
variable [PseudoMetricSpace A] [PseudoMetricSpace B] [PseudoMetricSpace C]

/-- Apply a unary map coordinatewise to reduced-product representatives. -/
def mapOnSequences (BB : BoundedMetricSort B) (f : A → B)
    {BA : BoundedMetricSort A} (x : ReducedSequence BA) : ReducedSequence BB :=
  fun n ↦ f (x n)

set_option maxHeartbeats 400000 in
/-- A uniformly continuous unary map remains uniformly continuous on sequence
representatives equipped with normalized ultralimit pseudometrics. -/
theorem mapOnSequences_uniformContinuous
    (BA : BoundedMetricSort A) (BB : BoundedMetricSort B)
    (f : A → B) (hf : UniformContinuous f) :
    UniformContinuous (mapOnSequences BB f : ReducedSequence BA → ReducedSequence BB) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨η, hη, hmodulus⟩ := Metric.uniformContinuous_iff.1 hf
    ((ε / 2) * BB.scale) (mul_pos (half_pos hε) BB.scale_pos)
  let δ := η / BA.scale
  have hδ : 0 < δ := div_pos hη BA.scale_pos
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  have hcoordinate : ∀ᶠ n in indexUltrafilter, dist (x n) (y n) < η := by
    have hnormalized :=
      (ReducedSequence.tendsto_normalizedDistance BA x y).eventually_lt_const hxy
    filter_upwards [hnormalized] with n hn
    exact (div_lt_div_iff_of_pos_right BA.scale_pos).1 hn
  have houtput : ∀ᶠ n in indexUltrafilter,
      (BB.normalizedDistance (f (x n)) (f (y n)) : ℝ) ≤ ε / 2 := by
    filter_upwards [hcoordinate] with n hn
    have hout := (hmodulus hn).le
    rw [BoundedMetricSort.coe_normalizedDistance, div_le_iff₀ BB.scale_pos]
    simpa [div_mul_eq_mul_div] using hout
  have hlimit := ReducedSequence.tendsto_normalizedDistance BB
    (mapOnSequences BB f x) (mapOnSequences BB f y)
  exact (isClosed_Iic.mem_of_tendsto hlimit houtput).trans_lt (half_lt_self hε)

/-- The map between reduced products induced coordinatewise by a uniformly
continuous unary map. -/
def map (BA : BoundedMetricSort A) (BB : BoundedMetricSort B)
    (f : A → B) (_hf : UniformContinuous f) : ReducedProduct BA → ReducedProduct BB :=
  SeparationQuotient.map (mapOnSequences BB f)

@[simp]
theorem map_mk (BA : BoundedMetricSort A) (BB : BoundedMetricSort B)
    (f : A → B) (hf : UniformContinuous f) (x : ReducedSequence BA) :
    map BA BB f hf (mk BA x) = mk BB (mapOnSequences BB f x) := by
  exact SeparationQuotient.map_mk (mapOnSequences_uniformContinuous BA BB f hf) x

/-- The induced unary map between reduced products is uniformly continuous. -/
theorem map_uniformContinuous (BA : BoundedMetricSort A) (BB : BoundedMetricSort B)
    (f : A → B) (hf : UniformContinuous f) :
    UniformContinuous (map BA BB f hf) :=
  SeparationQuotient.uniformContinuous_map _

/-- Apply a binary map coordinatewise to two reduced-product representatives. -/
def map₂OnSequences (BC : BoundedMetricSort C) (f : A → B → C)
    {BA : BoundedMetricSort A} {BB : BoundedMetricSort B}
    (x : ReducedSequence BA) (y : ReducedSequence BB) : ReducedSequence BC :=
  fun n ↦ f (x n) (y n)

set_option maxHeartbeats 400000 in
/-- A uniformly continuous binary map remains uniformly continuous on pairs
of sequence representatives equipped with normalized ultralimit
pseudometrics. -/
theorem map₂OnSequences_uniformContinuous
    (BA : BoundedMetricSort A) (BB : BoundedMetricSort B)
    (BC : BoundedMetricSort C) (f : A → B → C)
    (hf : UniformContinuous (Function.uncurry f)) :
    UniformContinuous
      (Function.uncurry
        (map₂OnSequences BC f : ReducedSequence BA → ReducedSequence BB →
          ReducedSequence BC)) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨η, hη, hmodulus⟩ := Metric.uniformContinuous_iff.1 hf
    ((ε / 2) * BC.scale) (mul_pos (half_pos hε) BC.scale_pos)
  let δ := min (η / BA.scale) (η / BB.scale)
  have hδ : 0 < δ := lt_min
    (div_pos hη BA.scale_pos) (div_pos hη BB.scale_pos)
  refine ⟨δ, hδ, ?_⟩
  rintro x y hxy
  have hxy' : max (dist x.1 y.1) (dist x.2 y.2) < δ := by
    simpa only [Prod.dist_eq] using hxy
  have hleft : ReducedSequence.sequenceDist BA x.1 y.1 < η / BA.scale :=
    (lt_of_le_of_lt (le_max_left _ _) hxy').trans_le (min_le_left _ _)
  have hright : ReducedSequence.sequenceDist BB x.2 y.2 < η / BB.scale :=
    (lt_of_le_of_lt (le_max_right _ _) hxy').trans_le (min_le_right _ _)
  have hleftCoordinate : ∀ᶠ n in indexUltrafilter, dist (x.1 n) (y.1 n) < η := by
    have hnormalized :=
      (ReducedSequence.tendsto_normalizedDistance BA x.1 y.1).eventually_lt_const hleft
    filter_upwards [hnormalized] with n hn
    exact (div_lt_div_iff_of_pos_right BA.scale_pos).1 hn
  have hrightCoordinate : ∀ᶠ n in indexUltrafilter, dist (x.2 n) (y.2 n) < η := by
    have hnormalized :=
      (ReducedSequence.tendsto_normalizedDistance BB x.2 y.2).eventually_lt_const hright
    filter_upwards [hnormalized] with n hn
    exact (div_lt_div_iff_of_pos_right BB.scale_pos).1 hn
  have houtput : ∀ᶠ n in indexUltrafilter,
      (BC.normalizedDistance (f (x.1 n) (x.2 n)) (f (y.1 n) (y.2 n)) : ℝ) ≤
        ε / 2 := by
    filter_upwards [hleftCoordinate, hrightCoordinate] with n hnleft hnright
    have hinput : dist (x.1 n, x.2 n) (y.1 n, y.2 n) < η := by
      rw [Prod.dist_eq]
      exact max_lt hnleft hnright
    have hout := (hmodulus hinput).le
    rw [BoundedMetricSort.coe_normalizedDistance, div_le_iff₀ BC.scale_pos]
    simpa [div_mul_eq_mul_div] using hout
  have hlimit := ReducedSequence.tendsto_normalizedDistance BC
    (map₂OnSequences BC f x.1 x.2) (map₂OnSequences BC f y.1 y.2)
  exact (isClosed_Iic.mem_of_tendsto hlimit houtput).trans_lt (half_lt_self hε)

/-- The map between reduced products induced coordinatewise by a uniformly
continuous binary map. -/
def map₂ (BA : BoundedMetricSort A) (BB : BoundedMetricSort B)
    (BC : BoundedMetricSort C) (f : A → B → C)
    (hf : UniformContinuous (Function.uncurry f)) :
    ReducedProduct BA → ReducedProduct BB → ReducedProduct BC :=
  SeparationQuotient.lift₂
    (fun x y ↦ mk BC (map₂OnSequences BC f x y)) <| by
      intro x y x' y' hx hy
      apply SeparationQuotient.mk_eq_mk.2
      exact (hx.prod hy).map
        (map₂OnSequences_uniformContinuous BA BB BC f hf).continuous

@[simp]
theorem map₂_mk (BA : BoundedMetricSort A) (BB : BoundedMetricSort B)
    (BC : BoundedMetricSort C) (f : A → B → C)
    (hf : UniformContinuous (Function.uncurry f))
    (x : ReducedSequence BA) (y : ReducedSequence BB) :
    map₂ BA BB BC f hf (mk BA x) (mk BB y) = mk BC (map₂OnSequences BC f x y) :=
  rfl

/-- The induced binary map between reduced products is uniformly continuous. -/
theorem map₂_uniformContinuous (BA : BoundedMetricSort A) (BB : BoundedMetricSort B)
    (BC : BoundedMetricSort C) (f : A → B → C)
    (hf : UniformContinuous (Function.uncurry f)) :
    UniformContinuous
      (Function.uncurry (map₂ BA BB BC f hf)) := by
  rw [map₂, SeparationQuotient.uniformContinuous_uncurry_lift₂]
  exact SeparationQuotient.uniformContinuous_mk.comp
    (map₂OnSequences_uniformContinuous BA BB BC f hf)

end ReducedProduct

end

end NormFormula.ContinuousLogic
