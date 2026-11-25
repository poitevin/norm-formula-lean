import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Metrizable.Urysohn
import NormFormula.ContinuousLogic.MultiPredicate

/-!
# Local parameter type spaces

For a binary bounded formula in one concrete many-predicate structure, its
local parameter type space is the pointwise closure of the evaluation profiles
realized by home parameters.  The ambient product of copies of `[0,1]` is
compact, so this gives a compact Hausdorff space without appealing to a
saturated model.  Every row defines a continuous coordinate-evaluation
function, and convergence in the local type space is exactly pointwise
convergence of these truth-value coordinates.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Filter Set TopologicalSpace
open scoped Topology

universe u v w

namespace MultiFormula

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.rowNonempty

/-- The `[0,1]`-valued profile on the home row sort realized by one parameter. -/
def parameterProfile {Symbol : Type w}
    (M : MultiStructure.{u, v, w} Symbol)
    (φ : MultiFormula Symbol 1 1) (parameter : M.Parameter) :
    M.Row → TruthValue :=
  fun row ↦ φ.realize M (fun _ ↦ row) (fun _ ↦ parameter)

@[simp]
theorem parameterProfile_apply {Symbol : Type w}
    (M : MultiStructure.{u, v, w} Symbol)
    (φ : MultiFormula Symbol 1 1) (parameter : M.Parameter) (row : M.Row) :
    parameterProfile M φ parameter row =
      φ.realize M (fun _ ↦ row) (fun _ ↦ parameter) :=
  rfl

/-- The local parameter type space of `φ` over the row sort of `M`: the
pointwise closure of the profiles realized by parameters of `M`. -/
def LocalParameterType {Symbol : Type w}
    (M : MultiStructure.{u, v, w} Symbol)
    (φ : MultiFormula Symbol 1 1) :=
  closure (Set.range (parameterProfile M φ))

/-- The local parameter type space is compact as a closed subspace of the
compact product `[0,1]^(M.Row)`. -/
instance localParameterTypeCompactSpace {Symbol : Type w}
    (M : MultiStructure.{u, v, w} Symbol)
    (φ : MultiFormula Symbol 1 1) :
    CompactSpace (LocalParameterType M φ) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

/-- A home parameter determines its realized local type. -/
def homeParameterType {Symbol : Type w}
    (M : MultiStructure.{u, v, w} Symbol)
    (φ : MultiFormula Symbol 1 1) (parameter : M.Parameter) :
    LocalParameterType M φ :=
  ⟨parameterProfile M φ parameter,
    subset_closure (Set.mem_range_self parameter)⟩

/-- The local type space is nonempty because the home parameter sort is. -/
instance localParameterTypeNonempty {Symbol : Type w}
    (M : MultiStructure.{u, v, w} Symbol)
    (φ : MultiFormula Symbol 1 1) :
    Nonempty (LocalParameterType M φ) := by
  let parameter := Classical.choice M.parameterNonempty
  exact ⟨homeParameterType M φ parameter⟩

/-- Home parameters are dense in their local parameter type space. -/
theorem denseRange_homeParameterType {Symbol : Type w}
    (M : MultiStructure.{u, v, w} Symbol)
    (φ : MultiFormula Symbol 1 1) :
    DenseRange (homeParameterType M φ) := by
  rw [DenseRange, Subtype.dense_iff]
  intro profile hprofile
  have himage :
      ((fun type : LocalParameterType M φ ↦
          (type : M.Row → TruthValue)) ''
        Set.range (homeParameterType M φ)) =
        Set.range (parameterProfile M φ) := by
    ext value
    constructor
    · rintro ⟨_, ⟨parameter, rfl⟩, rfl⟩
      exact ⟨parameter, rfl⟩
    · rintro ⟨parameter, rfl⟩
      exact ⟨homeParameterType M φ parameter, ⟨parameter, rfl⟩, rfl⟩
  rw [himage]
  exact hprofile

/-- In a Fréchet--Urysohn local type space (in particular, in the metrizable
spaces constructed below), every local type is the limit of a sequence of
realized home-parameter types. -/
theorem exists_homeParameter_sequence_tendsto {Symbol : Type w}
    (M : MultiStructure.{u, v, w} Symbol)
    (φ : MultiFormula Symbol 1 1)
    [FrechetUrysohnSpace (LocalParameterType M φ)]
    (type : LocalParameterType M φ) :
    ∃ parameters : ℕ → M.Parameter,
      Tendsto (fun n ↦ homeParameterType M φ (parameters n))
        atTop (nhds type) := by
  have hmem : type ∈
      closure (Set.range (homeParameterType M φ)) := by
    rw [(denseRange_homeParameterType M φ).closure_eq]
    exact Set.mem_univ type
  obtain ⟨types, htypes, htypesTendsto⟩ :=
    mem_closure_iff_seq_limit.mp hmem
  choose parameters hparameters using htypes
  refine ⟨parameters, ?_⟩
  have heq : (fun n ↦ homeParameterType M φ (parameters n)) = types := by
    funext n
    exact hparameters n
  rw [heq]
  exact htypesTendsto

/-- The truth-value coordinate at a fixed home row. -/
def localTypeTruthValue {Symbol : Type w}
    {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1}
    (row : M.Row) (type : LocalParameterType M φ) : TruthValue :=
  type.1 row

/-- The real-valued coordinate at a fixed home row. -/
def localTypeValue {Symbol : Type w}
    {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1}
    (row : M.Row) (type : LocalParameterType M φ) : ℝ :=
  localTypeTruthValue row type

/-- Truth-value evaluation at a fixed row is continuous on the local type
space. -/
theorem continuous_localTypeTruthValue {Symbol : Type w}
    {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1} (row : M.Row) :
    Continuous (localTypeTruthValue (M := M) (φ := φ) row) :=
  (continuous_apply row).comp continuous_subtype_val

/-- Real-valued evaluation at a fixed row is continuous on the local type
space. -/
theorem continuous_localTypeValue {Symbol : Type w}
    {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1} (row : M.Row) :
    Continuous (localTypeValue (M := M) (φ := φ) row) :=
  continuous_subtype_val.comp (continuous_localTypeTruthValue row)


@[simp]
theorem localTypeValue_homeParameterType {Symbol : Type w}
    (M : MultiStructure.{u, v, w} Symbol)
    (φ : MultiFormula Symbol 1 1) (row : M.Row)
    (parameter : M.Parameter) :
    localTypeValue row (homeParameterType M φ parameter) =
      φ.binaryValue M row parameter :=
  rfl


/-- The subtype topology on the local type space is precisely pointwise
convergence of all formula-evaluation coordinates. -/
theorem tendsto_localParameterType_iff_pointwise
    {Symbol : Type w} {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1} {ι : Type*} {l : Filter ι}
    {types : ι → LocalParameterType M φ}
    {type : LocalParameterType M φ} :
    Tendsto types l (𝓝 type) ↔
      ∀ row : M.Row,
        Tendsto (fun i ↦ localTypeTruthValue row (types i)) l
          (𝓝 (localTypeTruthValue row type)) := by
  rw [tendsto_subtype_rng, tendsto_pi_nhds]
  rfl

/-- All home-parameter profiles share one Lipschitz constant in the row
variable. This is the concrete countability hypothesis used to metrize local
type spaces over separable metric row sorts. -/
def ParameterProfilesLipschitzWith {Symbol : Type w}
    (M : MultiStructure.{u, v, w} Symbol)
    (φ : MultiFormula Symbol 1 1) (K : NNReal) : Prop :=
  ∀ parameter : M.Parameter, LipschitzWith K (parameterProfile M φ parameter)

/-- A pointwise limit type inherits every common Lipschitz bound satisfied by
the realized home-parameter profiles. -/
theorem lipschitzWith_localTypeProfile {Symbol : Type w}
    {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1} {K : NNReal}
    (hLipschitz : ParameterProfilesLipschitzWith M φ K)
    (type : LocalParameterType M φ) :
    LipschitzWith K type.1 := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let constraint : Set (M.Row → TruthValue) :=
    {profile | dist (profile x) (profile y) ≤ K * dist x y}
  have hclosed : IsClosed constraint := by
    exact isClosed_Iic.preimage ((continuous_apply x).dist (continuous_apply y))
  have hrange : Set.range (parameterProfile M φ) ⊆ constraint := by
    rintro _ ⟨parameter, rfl⟩
    change dist (parameterProfile M φ parameter x)
      (parameterProfile M φ parameter y) ≤ K * dist x y
    exact (hLipschitz parameter).dist_le_mul x y
  exact (closure_minimal hrange hclosed) type.2

/-- Every local type profile is continuous when the home profiles share a
Lipschitz constant. -/
theorem continuous_localTypeProfile {Symbol : Type w}
    {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1} {K : NNReal}
    (hLipschitz : ParameterProfilesLipschitzWith M φ K)
    (type : LocalParameterType M φ) :
    Continuous type.1 :=
  (lipschitzWith_localTypeProfile hLipschitz type).continuous

/-- Restriction of a local type profile to a chosen row sequence. -/
def localTypeDenseRestriction {Symbol : Type w}
    {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1} (rows : ℕ → M.Row) :
    LocalParameterType M φ → ℕ → TruthValue :=
  fun type n ↦ type.1 (rows n)

/-- Restriction to a row sequence is continuous in the pointwise topologies. -/
theorem continuous_localTypeDenseRestriction {Symbol : Type w}
    {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1} (rows : ℕ → M.Row) :
    Continuous (localTypeDenseRestriction (M := M) (φ := φ) rows) := by
  apply continuous_pi
  intro n
  exact (continuous_apply (rows n)).comp continuous_subtype_val

/-- Restriction to a dense row sequence is injective once all local profiles
are continuous. -/
theorem localTypeDenseRestriction_injective {Symbol : Type w}
    {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1} {K : NNReal}
    (hLipschitz : ParameterProfilesLipschitzWith M φ K)
    (rows : ℕ → M.Row) (hrows : DenseRange rows) :
    Function.Injective
      (localTypeDenseRestriction (M := M) (φ := φ) rows) := by
  intro first second heq
  apply Subtype.ext
  apply hrows.equalizer
    (continuous_localTypeProfile hLipschitz first)
    (continuous_localTypeProfile hLipschitz second)
  funext n
  exact congrFun heq n

/-- Over a separable row sort, a common Lipschitz modulus makes the compact
local parameter type space second countable. -/
@[reducible] noncomputable def localParameterTypeSecondCountableTopology
    {Symbol : Type w} (M : MultiStructure.{u, v, w} Symbol)
    (φ : MultiFormula Symbol 1 1) (K : NNReal)
    (hLipschitz : ParameterProfilesLipschitzWith M φ K)
    [hsep : SeparableSpace M.Row] :
    SecondCountableTopology (LocalParameterType M φ) := by
  let rows : ℕ → M.Row := denseSeq M.Row
  have hcontinuous : Continuous
      (localTypeDenseRestriction (M := M) (φ := φ) rows) :=
    continuous_localTypeDenseRestriction rows
  have hinjective : Function.Injective
      (localTypeDenseRestriction (M := M) (φ := φ) rows) :=
    localTypeDenseRestriction_injective hLipschitz rows
      (show DenseRange rows from denseRange_denseSeq M.Row)
  exact (hcontinuous.isClosedEmbedding hinjective).isEmbedding.secondCountableTopology

/-- Consequently, under the same hypotheses the compact local parameter type
space is metrizable. -/
@[reducible] noncomputable def localParameterTypeMetrizableSpace
    {Symbol : Type w} (M : MultiStructure.{u, v, w} Symbol)
    (φ : MultiFormula Symbol 1 1) (K : NNReal)
    (hLipschitz : ParameterProfilesLipschitzWith M φ K)
    [hsep : SeparableSpace M.Row] :
    MetrizableSpace (LocalParameterType M φ) := by
  letI : SecondCountableTopology (LocalParameterType M φ) :=
    localParameterTypeSecondCountableTopology M φ K hLipschitz
  infer_instance

section Map

universe u' v' w'


end Map

end MultiFormula

end

end NormFormula.ContinuousLogic
