import NormFormula.ContinuousLogic.BanachBallLimitOperations

/-!
# Banach operations on the closed ball-sorted limit carriers

The canonical limit points are dense and already closed under every typed
Banach operation.  Continuity therefore shows that the ambient operations
preserve the radius-wise closures.  We restrict all five operations to those
closed carriers and package the result as a complete rational ball system.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Set TopologicalSpace
open scoped Topology

universe u w

namespace BallWitnessIndexing

variable {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
  {M : BallStructure.{u, w} Symbol symbolRadius}

/-- The distinguished zero belongs to every closed generated radius sort. -/
theorem zero_mem_limitCarrier [Encodable Symbol]
    (initial : BallWitnessIndexing M) (radius : ℚ≥0) :
    M.zero radius ∈ initial.LimitCarrier radius := by
  apply subset_closure
  exact ⟨initial.limitZero radius, initial.limitMap_limitZero radius⟩

/-- Ambient inclusion preserves the closed generated carriers. -/
theorem inclusion_mem_limitCarrier [Encodable Symbol]
    (initial : BallWitnessIndexing M) {r s : ℚ≥0} (h : r ≤ s)
    (point : initial.LimitCarrier r) :
    M.inclusion h point.1 ∈ initial.LimitCarrier s := by
  have hmaps : Set.MapsTo (M.inclusion h)
      (Set.range (initial.limitMap r))
      (Set.range (initial.limitMap s)) := by
    rintro _ ⟨index, rfl⟩
    exact ⟨initial.limitInclusion h index,
      initial.limitMap_limitInclusion h index⟩
  exact hmaps.closure (M.inclusion_uniformContinuous h).continuous point.2

/-- Ambient negation preserves each closed generated radius sort. -/
theorem neg_mem_limitCarrier [Encodable Symbol]
    (initial : BallWitnessIndexing M) (radius : ℚ≥0)
    (point : initial.LimitCarrier radius) :
    M.neg radius point.1 ∈ initial.LimitCarrier radius := by
  have hmaps : Set.MapsTo (M.neg radius)
      (Set.range (initial.limitMap radius))
      (Set.range (initial.limitMap radius)) := by
    rintro _ ⟨index, rfl⟩
    exact ⟨initial.limitNeg radius index,
      initial.limitMap_limitNeg radius index⟩
  exact hmaps.closure (M.neg_uniformContinuous radius).continuous point.2

/-- Ambient addition maps a pair of closed generated carriers into the
closed carrier of the sum radius. -/
theorem add_mem_limitCarrier [Encodable Symbol]
    (initial : BallWitnessIndexing M) (r s : ℚ≥0)
    (left : initial.LimitCarrier r) (right : initial.LimitCarrier s) :
    M.add r s (left.1, right.1) ∈ initial.LimitCarrier (r + s) := by
  have hmaps : Set.MapsTo (M.add r s)
      (Set.range (initial.limitMap r) ×ˢ
        Set.range (initial.limitMap s))
      (Set.range (initial.limitMap (r + s))) := by
    rintro ⟨x, y⟩ ⟨⟨leftIndex, hleft⟩, ⟨rightIndex, hright⟩⟩
    change initial.limitMap r leftIndex = x at hleft
    change initial.limitMap s rightIndex = y at hright
    subst x
    subst y
    exact ⟨initial.limitAdd r s leftIndex rightIndex,
      initial.limitMap_limitAdd r s leftIndex rightIndex⟩
  have hpair : (left.1, right.1) ∈
      closure (Set.range (initial.limitMap r) ×ˢ
        Set.range (initial.limitMap s)) := by
    rw [closure_prod_eq]
    exact ⟨left.2, right.2⟩
  exact hmaps.closure (M.add_uniformContinuous r s).continuous hpair

/-- Ambient rational scalar multiplication preserves the closed generated
carriers in its exact output radius. -/
theorem smul_mem_limitCarrier [Encodable Symbol]
    (initial : BallWitnessIndexing M) (q : ℚ) (radius : ℚ≥0)
    (point : initial.LimitCarrier radius) :
    M.smul q radius point.1 ∈
      initial.LimitCarrier (q.nnabs * radius) := by
  have hmaps : Set.MapsTo (M.smul q radius)
      (Set.range (initial.limitMap radius))
      (Set.range (initial.limitMap (q.nnabs * radius))) := by
    rintro _ ⟨index, rfl⟩
    exact ⟨initial.limitSmul q radius index,
      initial.limitMap_limitSmul q radius index⟩
  exact hmaps.closure (M.smul_uniformContinuous q radius).continuous point.2

/-- Restricted inclusion between closed generated radius sorts. -/
def carrierInclusion [Encodable Symbol] (initial : BallWitnessIndexing M)
    {r s : ℚ≥0} (h : r ≤ s) :
    initial.LimitCarrier r → initial.LimitCarrier s :=
  fun point ↦ ⟨M.inclusion h point.1,
    initial.inclusion_mem_limitCarrier h point⟩

/-- Restricted distinguished zero. -/
def carrierZero [Encodable Symbol] (initial : BallWitnessIndexing M)
    (radius : ℚ≥0) : initial.LimitCarrier radius :=
  ⟨M.zero radius, initial.zero_mem_limitCarrier radius⟩

/-- Restricted negation. -/
def carrierNeg [Encodable Symbol] (initial : BallWitnessIndexing M)
    (radius : ℚ≥0) :
    initial.LimitCarrier radius → initial.LimitCarrier radius :=
  fun point ↦ ⟨M.neg radius point.1,
    initial.neg_mem_limitCarrier radius point⟩

/-- Restricted addition. -/
def carrierAdd [Encodable Symbol] (initial : BallWitnessIndexing M)
    (r s : ℚ≥0) : initial.LimitCarrier r × initial.LimitCarrier s →
      initial.LimitCarrier (r + s) :=
  fun pair ↦ ⟨M.add r s (pair.1.1, pair.2.1),
    initial.add_mem_limitCarrier r s pair.1 pair.2⟩

/-- Restricted rational scalar multiplication. -/
def carrierSmul [Encodable Symbol] (initial : BallWitnessIndexing M)
    (q : ℚ) (radius : ℚ≥0) : initial.LimitCarrier radius →
      initial.LimitCarrier (q.nnabs * radius) :=
  fun point ↦ ⟨M.smul q radius point.1,
    initial.smul_mem_limitCarrier q radius point⟩

@[simp]
theorem carrierInclusion_val [Encodable Symbol]
    (initial : BallWitnessIndexing M) {r s : ℚ≥0} (h : r ≤ s)
    (point : initial.LimitCarrier r) :
    (initial.carrierInclusion h point : M.Ball s) =
      M.inclusion h point.1 :=
  rfl

@[simp]
theorem carrierZero_val [Encodable Symbol]
    (initial : BallWitnessIndexing M) (radius : ℚ≥0) :
    (initial.carrierZero radius : M.Ball radius) = M.zero radius :=
  rfl

@[simp]
theorem carrierNeg_val [Encodable Symbol]
    (initial : BallWitnessIndexing M) (radius : ℚ≥0)
    (point : initial.LimitCarrier radius) :
    (initial.carrierNeg radius point : M.Ball radius) =
      M.neg radius point.1 :=
  rfl

@[simp]
theorem carrierAdd_val [Encodable Symbol]
    (initial : BallWitnessIndexing M) (r s : ℚ≥0)
    (pair : initial.LimitCarrier r × initial.LimitCarrier s) :
    (initial.carrierAdd r s pair : M.Ball (r + s)) =
      M.add r s (pair.1.1, pair.2.1) :=
  rfl

@[simp]
theorem carrierSmul_val [Encodable Symbol]
    (initial : BallWitnessIndexing M) (q : ℚ) (radius : ℚ≥0)
    (point : initial.LimitCarrier radius) :
    (initial.carrierSmul q radius point : M.Ball (q.nnabs * radius)) =
      M.smul q radius point.1 :=
  rfl

theorem carrierInclusion_uniformContinuous [Encodable Symbol]
    (initial : BallWitnessIndexing M) {r s : ℚ≥0} (h : r ≤ s) :
    UniformContinuous (initial.carrierInclusion h) :=
  ((M.inclusion_uniformContinuous h).comp
    uniformContinuous_subtype_val).subtype_mk _

theorem carrierNeg_uniformContinuous [Encodable Symbol]
    (initial : BallWitnessIndexing M) (radius : ℚ≥0) :
    UniformContinuous (initial.carrierNeg radius) :=
  ((M.neg_uniformContinuous radius).comp
    uniformContinuous_subtype_val).subtype_mk _

theorem carrierAdd_uniformContinuous [Encodable Symbol]
    (initial : BallWitnessIndexing M) (r s : ℚ≥0) :
    UniformContinuous (initial.carrierAdd r s) := by
  have hleft : UniformContinuous
      (fun pair : initial.LimitCarrier r × initial.LimitCarrier s ↦
        (pair.1.1 : M.Ball r)) :=
    uniformContinuous_subtype_val.comp uniformContinuous_fst
  have hright : UniformContinuous
      (fun pair : initial.LimitCarrier r × initial.LimitCarrier s ↦
        (pair.2.1 : M.Ball s)) :=
    uniformContinuous_subtype_val.comp uniformContinuous_snd
  exact ((M.add_uniformContinuous r s).comp
    (hleft.prodMk hright)).subtype_mk _

theorem carrierSmul_uniformContinuous [Encodable Symbol]
    (initial : BallWitnessIndexing M) (q : ℚ) (radius : ℚ≥0) :
    UniformContinuous (initial.carrierSmul q radius) :=
  ((M.smul_uniformContinuous q radius).comp
    uniformContinuous_subtype_val).subtype_mk _

/-- The complete rational ball system obtained by restricting the ambient
system to the closed generated carriers. -/
def limitRationalBallSystem [Encodable Symbol]
    (initial : BallWitnessIndexing M) : RationalBallSystem where
  Ball := fun radius ↦ ↥(initial.LimitCarrier radius)
  ballPseudoMetricSpace := fun _ ↦ inferInstance
  ballCompleteSpace := fun radius ↦ initial.limitCarrierCompleteSpace radius
  ballNonempty := fun radius ↦ ⟨initial.carrierZero radius⟩
  sortBound := M.sortBound
  sortBound_pos := M.sortBound_pos
  dist_le_sortBound := by
    intro radius x y
    exact M.dist_le_sortBound radius x.1 y.1
  inclusion := fun {_ _} h ↦ initial.carrierInclusion h
  zero := initial.carrierZero
  neg := initial.carrierNeg
  add := initial.carrierAdd
  smul := initial.carrierSmul
  inclusion_uniformContinuous := initial.carrierInclusion_uniformContinuous
  neg_uniformContinuous := initial.carrierNeg_uniformContinuous
  add_uniformContinuous := initial.carrierAdd_uniformContinuous
  smul_uniformContinuous := initial.carrierSmul_uniformContinuous

end BallWitnessIndexing

end

end NormFormula.ContinuousLogic
