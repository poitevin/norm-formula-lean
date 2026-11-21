import Mathlib.Topology.MetricSpace.Completion
import NormFormula.ContinuousLogic.BanachBallSystem
import NormFormula.ContinuousLogic.ReducedProductMap

/-!
# Completed reduced products of rational-ball systems

For every rational-radius sort of a `RationalBallSystem`, take its normalized
metric reduced product and then its metric completion.  Completing at this
stage avoids assuming the completeness theorem for metric ultraproducts; the
completion functor extends uniformly continuous unary and binary maps, so all
five Banach operations still lift coherently at the semantic level.

The completed reduced sorts have diameter at most one because the reduced
metric is the ultralimit of normalized truth-value distances.  They therefore
assemble into another `RationalBallSystem`, with constant sort bound `1`.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open scoped Topology
open UniformSpace

universe u

namespace ReducedProduct

variable {A : Type u} [PseudoMetricSpace A]

/-- Every normalized metric reduced product has diameter at most one. -/
theorem dist_le_one (BA : BoundedMetricSort A) (x y : ReducedProduct BA) :
    dist x y ≤ 1 := by
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk x
  obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk y
  rw [SeparationQuotient.dist_mk]
  exact (ultralimit fun n ↦ BA.normalizedDistance (x n) (y n)).property.2

/-- The completed normalized reduced product of one bounded metric sort. -/
abbrev Completed (BA : BoundedMetricSort A) := Completion (ReducedProduct BA)

/-- The canonical image of a sequence representative in the completed
reduced product. -/
def completedMk (BA : BoundedMetricSort A) (x : ReducedSequence BA) : Completed BA :=
  (mk BA x : Completed BA)

/-- The canonical image of a constant sequence in the completed reduced
product. -/
def completedConst (BA : BoundedMetricSort A) (x : A) : Completed BA :=
  (const BA x : Completed BA)

/-- Completion does not enlarge the normalized diameter bound. -/
theorem completed_dist_le_one (BA : BoundedMetricSort A) (x y : Completed BA) :
    dist x y ≤ 1 := by
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_le continuous_dist continuous_const
  | ih x y =>
      rw [Completion.dist_eq]
      exact dist_le_one BA x y

variable {B : Type u} {C : Type u}
variable [PseudoMetricSpace B] [PseudoMetricSpace C]

/-- Extend a coordinatewise unary reduced-product map to the completions. -/
def completedMap (BA : BoundedMetricSort A) (BB : BoundedMetricSort B)
    (f : A → B) (hf : UniformContinuous f) : Completed BA → Completed BB :=
  Completion.map (ReducedProduct.map BA BB f hf)

/-- A completed unary reduced-product map is uniformly continuous. -/
theorem completedMap_uniformContinuous
    (BA : BoundedMetricSort A) (BB : BoundedMetricSort B)
    (f : A → B) (hf : UniformContinuous f) :
    UniformContinuous (completedMap BA BB f hf) :=
  Completion.uniformContinuous_map

@[simp]
theorem completedMap_mk
    (BA : BoundedMetricSort A) (BB : BoundedMetricSort B)
    (f : A → B) (hf : UniformContinuous f) (x : ReducedSequence BA) :
    completedMap BA BB f hf (completedMk BA x) =
      completedMk BB (mapOnSequences BB f x) := by
  rw [completedMap, completedMk, Completion.map_coe
    (ReducedProduct.map_uniformContinuous BA BB f hf), ReducedProduct.map_mk]
  rfl

/-- Extend a coordinatewise binary reduced-product map to the completions. -/
def completedMap₂ (BA : BoundedMetricSort A) (BB : BoundedMetricSort B)
    (BC : BoundedMetricSort C) (f : A → B → C)
    (hf : UniformContinuous (Function.uncurry f)) :
    Completed BA → Completed BB → Completed BC :=
  Completion.map₂ (ReducedProduct.map₂ BA BB BC f hf)

/-- A completed binary reduced-product map is jointly uniformly continuous. -/
theorem completedMap₂_uniformContinuous
    (BA : BoundedMetricSort A) (BB : BoundedMetricSort B)
    (BC : BoundedMetricSort C) (f : A → B → C)
    (hf : UniformContinuous (Function.uncurry f)) :
    UniformContinuous (Function.uncurry (completedMap₂ BA BB BC f hf)) :=
  Completion.uniformContinuous_map₂ _

@[simp]
theorem completedMap₂_mk
    (BA : BoundedMetricSort A) (BB : BoundedMetricSort B)
    (BC : BoundedMetricSort C) (f : A → B → C)
    (hf : UniformContinuous (Function.uncurry f))
    (x : ReducedSequence BA) (y : ReducedSequence BB) :
    completedMap₂ BA BB BC f hf (completedMk BA x) (completedMk BB y) =
      completedMk BC (map₂OnSequences BC f x y) := by
  simp only [completedMap₂, completedMk]
  rw [Completion.map₂_coe_coe]
  · rw [ReducedProduct.map₂_mk]
  · exact ReducedProduct.map₂_uniformContinuous BA BB BC f hf

end ReducedProduct

namespace RationalBallSystem

variable (M : RationalBallSystem.{u})

/-- The bounded metric sort attached to one ball of a rational-ball system. -/
def reducedBound (r : ℚ≥0) : BoundedMetricSort (M.Ball r) where
  scale := M.sortBound r
  scale_pos := M.sortBound_pos r
  dist_le_scale := M.dist_le_sortBound r

/-- The completed normalized reduced-product carrier at radius `r`. -/
abbrev ReducedBall (r : ℚ≥0) := ReducedProduct.Completed (M.reducedBound r)

/-- The completed metric reduced product of a rational-ball system. -/
def reducedProduct : RationalBallSystem where
  Ball := M.ReducedBall
  ballPseudoMetricSpace := fun _ ↦ inferInstance
  ballCompleteSpace := fun _ ↦ inferInstance
  ballNonempty := fun r ↦ by
    exact (Completion.nonempty_completion_iff _).2 inferInstance
  sortBound := fun _ ↦ 1
  sortBound_pos := fun _ ↦ one_pos
  dist_le_sortBound := fun r ↦ ReducedProduct.completed_dist_le_one (M.reducedBound r)
  inclusion := fun {_ _} h ↦
    ReducedProduct.completedMap _ _ (M.inclusion h) (M.inclusion_uniformContinuous h)
  zero := fun r ↦ ReducedProduct.completedConst (M.reducedBound r) (M.zero r)
  neg := fun r ↦
    ReducedProduct.completedMap _ _ (M.neg r) (M.neg_uniformContinuous r)
  add := fun r s ↦ Function.uncurry <|
    ReducedProduct.completedMap₂ _ _ _
      (fun x y ↦ M.add r s (x, y)) (by
        simpa only [Function.uncurry_curry] using M.add_uniformContinuous r s)
  smul := fun q r ↦
    ReducedProduct.completedMap _ _ (M.smul q r) (M.smul_uniformContinuous q r)
  inclusion_uniformContinuous := fun {_ _} h ↦
    ReducedProduct.completedMap_uniformContinuous _ _
      (M.inclusion h) (M.inclusion_uniformContinuous h)
  neg_uniformContinuous := fun r ↦
    ReducedProduct.completedMap_uniformContinuous _ _ (M.neg r) (M.neg_uniformContinuous r)
  add_uniformContinuous := fun r s ↦
    ReducedProduct.completedMap₂_uniformContinuous _ _ _
      (fun x y ↦ M.add r s (x, y)) (by
        simpa only [Function.uncurry_curry] using M.add_uniformContinuous r s)
  smul_uniformContinuous := fun q r ↦
    ReducedProduct.completedMap_uniformContinuous _ _
      (M.smul q r) (M.smul_uniformContinuous q r)

/-- The diagonal embedding of one original ball into its completed reduced
product. -/
def reducedConst (r : ℚ≥0) : M.Ball r → (M.reducedProduct).Ball r :=
  ReducedProduct.completedConst (M.reducedBound r)

@[simp]
theorem reducedProduct_inclusion_mk {r s : ℚ≥0} (h : r ≤ s)
    (x : ReducedSequence (M.reducedBound r)) :
    (M.reducedProduct).inclusion h
        (ReducedProduct.completedMk (M.reducedBound r) x) =
      ReducedProduct.completedMk (M.reducedBound s)
        (ReducedProduct.mapOnSequences (M.reducedBound s) (M.inclusion h) x) := by
  exact ReducedProduct.completedMap_mk _ _ _ _ x

@[simp]
theorem reducedProduct_zero (r : ℚ≥0) :
    (M.reducedProduct).zero r = M.reducedConst r (M.zero r) :=
  rfl

@[simp]
theorem reducedProduct_neg_mk (r : ℚ≥0)
    (x : ReducedSequence (M.reducedBound r)) :
    (M.reducedProduct).neg r
        (ReducedProduct.completedMk (M.reducedBound r) x) =
      ReducedProduct.completedMk (M.reducedBound r)
        (ReducedProduct.mapOnSequences (M.reducedBound r) (M.neg r) x) := by
  exact ReducedProduct.completedMap_mk _ _ _ _ x

@[simp]
theorem reducedProduct_add_mk (r s : ℚ≥0)
    (x : ReducedSequence (M.reducedBound r))
    (y : ReducedSequence (M.reducedBound s)) :
    (M.reducedProduct).add r s
        (ReducedProduct.completedMk (M.reducedBound r) x,
          ReducedProduct.completedMk (M.reducedBound s) y) =
      ReducedProduct.completedMk (M.reducedBound (r + s))
        (ReducedProduct.map₂OnSequences (M.reducedBound (r + s))
          (fun a b ↦ M.add r s (a, b)) x y) := by
  exact ReducedProduct.completedMap₂_mk _ _ _ _ _ x y

@[simp]
theorem reducedProduct_smul_mk (q : ℚ) (r : ℚ≥0)
    (x : ReducedSequence (M.reducedBound r)) :
    (M.reducedProduct).smul q r
        (ReducedProduct.completedMk (M.reducedBound r) x) =
      ReducedProduct.completedMk (M.reducedBound (q.nnabs * r))
        (ReducedProduct.mapOnSequences (M.reducedBound (q.nnabs * r))
          (M.smul q r) x) := by
  exact ReducedProduct.completedMap_mk _ _ _ _ x

@[simp]
theorem reducedProduct_inclusion_const {r s : ℚ≥0} (h : r ≤ s) (x : M.Ball r) :
    (M.reducedProduct).inclusion h (M.reducedConst r x) =
      M.reducedConst s (M.inclusion h x) := by
  exact reducedProduct_inclusion_mk M h (fun _ ↦ x)

@[simp]
theorem reducedProduct_neg_const (r : ℚ≥0) (x : M.Ball r) :
    (M.reducedProduct).neg r (M.reducedConst r x) =
      M.reducedConst r (M.neg r x) := by
  exact reducedProduct_neg_mk M r (fun _ ↦ x)

@[simp]
theorem reducedProduct_add_const (r s : ℚ≥0) (x : M.Ball r) (y : M.Ball s) :
    (M.reducedProduct).add r s (M.reducedConst r x, M.reducedConst s y) =
      M.reducedConst (r + s) (M.add r s (x, y)) := by
  exact reducedProduct_add_mk M r s (fun _ ↦ x) (fun _ ↦ y)

@[simp]
theorem reducedProduct_smul_const (q : ℚ) (r : ℚ≥0) (x : M.Ball r) :
    (M.reducedProduct).smul q r (M.reducedConst r x) =
      M.reducedConst (q.nnabs * r) (M.smul q r x) := by
  exact reducedProduct_smul_mk M q r (fun _ ↦ x)

end RationalBallSystem

end


end NormFormula.ContinuousLogic
