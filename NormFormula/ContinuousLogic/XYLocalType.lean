import NormFormula.Analytic.XYSpace
import NormFormula.ContinuousLogic.NormAddLocalType
import NormFormula.ModelTheory.ConnectiveClosure

/-!
# Joint factor types for the bounded direct sum

A parameter in the radius-`R` ball of `X ⊕₂ Y` determines one local norm type
in each radius-`R` factor ball.  The closure of these jointly realized pairs,
rather than the full product of the two factor type spaces, is the correct
compact domain for the direct-sum norm formula: arbitrary independent factor
parameters of norm at most `R` need not have ℓ₂-sum norm at most `R`.
-/

namespace NormFormula.XY

noncomputable section

open Set TopologicalSpace
open scoped ENNReal Topology
open NormFormula.ContinuousLogic

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.rowNonempty

/-- The first coordinate of a point in the direct-sum radius-`R` ball remains
in the radius-`R` ball of `XSpace`. -/
def positiveNormBallFst (R : ℝ)
    (z : PositiveNormBall XYSpace R) : PositiveNormBall X.XSpace R :=
  ⟨z.1.fst, (WithLp.norm_fst_le X.XSpace z.1).trans z.2⟩

/-- The second coordinate of a point in the direct-sum radius-`R` ball remains
in the radius-`R` ball of `Y`. -/
def positiveNormBallSnd (R : ℝ)
    (z : PositiveNormBall XYSpace R) : PositiveNormBall HalfGraph.Y R :=
  ⟨z.1.snd, (WithLp.norm_snd_le X.XSpace z.1).trans z.2⟩

@[simp]
theorem positiveNormBallFst_value (R : ℝ)
    (z : PositiveNormBall XYSpace R) :
    (positiveNormBallFst R z).1 = z.1.fst :=
  rfl

@[simp]
theorem positiveNormBallSnd_value (R : ℝ)
    (z : PositiveNormBall XYSpace R) :
    (positiveNormBallSnd R z).1 = z.1.snd :=
  rfl

/-- The local parameter type space of normalized norm addition on the
radius-`R` ball of `XSpace`. -/
abbrev XNormLocalParameterType (R : ℝ) (hR : 0 < R) :=
  MultiFormula.LocalParameterType
    (normAddMultiStructure (E := X.XSpace) R hR) normAddMultiFormula

/-- The corresponding local parameter type space for `Y`. -/
abbrev YNormLocalParameterType (R : ℝ) (hR : 0 < R) :=
  MultiFormula.LocalParameterType
    (normAddMultiStructure (E := HalfGraph.Y) R hR) normAddMultiFormula

/-- The local parameter type space of normalized norm addition on the
direct-sum radius-`R` ball. -/
abbrev XYNormLocalParameterType (R : ℝ) (hR : 0 < R) :=
  MultiFormula.LocalParameterType
    (normAddMultiStructure (E := XYSpace) R hR) normAddMultiFormula

/-- One direct-sum parameter gives the pair of its realized coordinate norm
types in the two common one-symbol factor structures. -/
def homeFactorTypePair (R : ℝ) (hR : 0 < R)
    (parameter : PositiveNormBall XYSpace R) :
    XNormLocalParameterType R hR × YNormLocalParameterType R hR :=
  (MultiFormula.homeParameterType
      (normAddMultiStructure (E := X.XSpace) R hR) normAddMultiFormula
      (positiveNormBallFst R parameter),
    MultiFormula.homeParameterType
      (normAddMultiStructure (E := HalfGraph.Y) R hR) normAddMultiFormula
      (positiveNormBallSnd R parameter))

/-- Joint factor types are precisely the closure of coordinate type pairs
realized by parameters from the same direct-sum radius-`R` ball. -/
def JointNormFactorType (R : ℝ) (hR : 0 < R) :=
  closure (Set.range (homeFactorTypePair R hR))

/-- The jointly realizable factor-type space is compact. -/
instance jointNormFactorTypeCompactSpace (R : ℝ) (hR : 0 < R) :
    CompactSpace (JointNormFactorType R hR) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

/-- A home direct-sum parameter determines a jointly realizable factor type. -/
def homeJointNormFactorType (R : ℝ) (hR : 0 < R)
    (parameter : PositiveNormBall XYSpace R) :
    JointNormFactorType R hR :=
  ⟨homeFactorTypePair R hR parameter,
    subset_closure (Set.mem_range_self parameter)⟩

/-- The joint factor-type space is nonempty. -/
instance jointNormFactorTypeNonempty (R : ℝ) (hR : 0 < R) :
    Nonempty (JointNormFactorType R hR) :=
  ⟨homeJointNormFactorType R hR
    ⟨0, by simpa using hR.le⟩⟩

/-- Joint factor types realized by home direct-sum parameters are dense. -/
theorem denseRange_homeJointNormFactorType (R : ℝ) (hR : 0 < R) :
    DenseRange (homeJointNormFactorType R hR) := by
  rw [DenseRange, Subtype.dense_iff]
  intro pair hpair
  have himage :
      ((fun type : JointNormFactorType R hR ↦
          (type : XNormLocalParameterType R hR ×
            YNormLocalParameterType R hR)) ''
        Set.range (homeJointNormFactorType R hR)) =
        Set.range (homeFactorTypePair R hR) := by
    ext value
    constructor
    · rintro ⟨_, ⟨parameter, rfl⟩, rfl⟩
      exact ⟨parameter, rfl⟩
    · rintro ⟨parameter, rfl⟩
      exact ⟨homeJointNormFactorType R hR parameter,
        ⟨parameter, rfl⟩, rfl⟩
  rw [himage]
  exact hpair

@[simp]
theorem homeJointNormFactorType_value (R : ℝ) (hR : 0 < R)
    (parameter : PositiveNormBall XYSpace R) :
    (homeJointNormFactorType R hR parameter).1 =
      homeFactorTypePair R hR parameter :=
  rfl

/-- At realized parameters, normalized norm addition on the direct sum is the
Euclidean combination of the two normalized factor values. -/
theorem euclidean_factor_normAddMultiFormula_value
    (R : ℝ) (hR : 0 < R)
    (row parameter : PositiveNormBall XYSpace R) :
    NormFormula.euclideanConnective
        (normAddMultiFormula.binaryValue
          (normAddMultiStructure (E := X.XSpace) R hR)
          (positiveNormBallFst R row) (positiveNormBallFst R parameter))
        (normAddMultiFormula.binaryValue
          (normAddMultiStructure (E := HalfGraph.Y) R hR)
          (positiveNormBallSnd R row) (positiveNormBallSnd R parameter)) =
      normAddMultiFormula.binaryValue
        (normAddMultiStructure (E := XYSpace) R hR) row parameter := by
  have hdenom : 0 < 2 * R := by positivity
  have hsum : 0 ≤
      ‖row.1.fst + parameter.1.fst‖ ^ 2 +
        ‖row.1.snd + parameter.1.snd‖ ^ 2 := by positivity
  rw [normAddMultiFormula_value, normAddMultiFormula_value,
    normAddMultiFormula_value, NormFormula.euclideanConnective]
  change
    Real.sqrt
        ((‖row.1.fst + parameter.1.fst‖ / (2 * R)) ^ 2 +
          (‖row.1.snd + parameter.1.snd‖ / (2 * R)) ^ 2) =
      ‖row.1 + parameter.1‖ / (2 * R)
  have hradicand :
      (‖row.1.fst + parameter.1.fst‖ / (2 * R)) ^ 2 +
          (‖row.1.snd + parameter.1.snd‖ / (2 * R)) ^ 2 =
        (‖row.1.fst + parameter.1.fst‖ ^ 2 +
          ‖row.1.snd + parameter.1.snd‖ ^ 2) / (2 * R) ^ 2 := by
    field_simp [ne_of_gt hdenom]
  rw [hradicand, Real.sqrt_div hsum, Real.sqrt_sq hdenom.le]
  have hprod :
      ‖row.1 + parameter.1‖ ^ 2 =
        ‖row.1.fst + parameter.1.fst‖ ^ 2 +
          ‖row.1.snd + parameter.1.snd‖ ^ 2 := by
    simpa using WithLp.prod_norm_sq_eq_of_L2 (row.1 + parameter.1)
  rw [← hprod, Real.sqrt_sq (norm_nonneg _)]

/-- Evaluation of a joint factor type at a direct-sum row, using the
Euclidean combination of the two factor local-type evaluations. -/
def jointNormFactorValue (R : ℝ) (hR : 0 < R)
    (row : PositiveNormBall XYSpace R)
    (type : JointNormFactorType R hR) : ℝ :=
  NormFormula.euclideanConnective
    (MultiFormula.localTypeValue (positiveNormBallFst R row) type.1.1)
    (MultiFormula.localTypeValue (positiveNormBallSnd R row) type.1.2)

/-- Joint-factor evaluation at a fixed row is continuous. -/
theorem continuous_jointNormFactorValue (R : ℝ) (hR : 0 < R)
    (row : PositiveNormBall XYSpace R) :
    Continuous (jointNormFactorValue R hR row) := by
  have hx : Continuous fun type : JointNormFactorType R hR ↦
      MultiFormula.localTypeValue (positiveNormBallFst R row) type.1.1 :=
    (MultiFormula.continuous_localTypeValue
      (M := normAddMultiStructure (E := X.XSpace) R hR)
      (φ := normAddMultiFormula) (positiveNormBallFst R row)).comp
      (continuous_fst.comp continuous_subtype_val)
  have hy : Continuous fun type : JointNormFactorType R hR ↦
      MultiFormula.localTypeValue (positiveNormBallSnd R row) type.1.2 :=
    (MultiFormula.continuous_localTypeValue
      (M := normAddMultiStructure (E := HalfGraph.Y) R hR)
      (φ := normAddMultiFormula) (positiveNormBallSnd R row)).comp
      (continuous_snd.comp continuous_subtype_val)
  exact NormFormula.euclideanConnective_uniformContinuous.continuous.comp
    (hx.prodMk hy)

/-- The Euclidean value of a jointly realizable factor type remains in
`[0,1]` at every direct-sum row. The upper bound is first checked on home
parameters by the exact ℓ₂ identity and then extended over their dense
closure. -/
theorem jointNormFactorValue_mem_Icc (R : ℝ) (hR : 0 < R)
    (row : PositiveNormBall XYSpace R)
    (type : JointNormFactorType R hR) :
    jointNormFactorValue R hR row type ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  let constraint : Set (JointNormFactorType R hR) :=
    {jointType | jointNormFactorValue R hR row jointType ≤ 1}
  have hclosed : IsClosed constraint :=
    isClosed_Iic.preimage (continuous_jointNormFactorValue R hR row)
  have hrange : Set.range (homeJointNormFactorType R hR) ⊆ constraint := by
    rintro _ ⟨parameter, rfl⟩
    change jointNormFactorValue R hR row
      (homeJointNormFactorType R hR parameter) ≤ 1
    rw [jointNormFactorValue]
    change NormFormula.euclideanConnective
        (normAddMultiFormula.binaryValue
          (normAddMultiStructure (E := X.XSpace) R hR)
          (positiveNormBallFst R row) (positiveNormBallFst R parameter))
        (normAddMultiFormula.binaryValue
          (normAddMultiStructure (E := HalfGraph.Y) R hR)
          (positiveNormBallSnd R row) (positiveNormBallSnd R parameter)) ≤ 1
    rw [euclidean_factor_normAddMultiFormula_value]
    exact (normAddTruth R hR row parameter).property.2
  have hmem : type ∈ closure (Set.range (homeJointNormFactorType R hR)) := by
    rw [(denseRange_homeJointNormFactorType R hR).closure_eq]
    exact Set.mem_univ type
  exact closure_minimal hrange hclosed hmem

/-- The `[0,1]`-valued profile on direct-sum rows determined by a joint factor
type. -/
def jointNormFactorProfile (R : ℝ) (hR : 0 < R)
    (type : JointNormFactorType R hR) :
    PositiveNormBall XYSpace R → TruthValue :=
  fun row ↦ ⟨jointNormFactorValue R hR row type,
    jointNormFactorValue_mem_Icc R hR row type⟩

/-- Joint-factor profiles vary continuously in the pointwise product
topology. -/
theorem continuous_jointNormFactorProfile (R : ℝ) (hR : 0 < R) :
    Continuous (jointNormFactorProfile R hR) := by
  apply continuous_pi
  intro row
  exact (continuous_jointNormFactorValue R hR row).subtype_mk _

/-- On a home parameter, the joint-factor profile is exactly the realized
direct-sum norm profile. -/
theorem jointNormFactorProfile_homeJointNormFactorType
    (R : ℝ) (hR : 0 < R)
    (parameter : PositiveNormBall XYSpace R) :
    jointNormFactorProfile R hR
        (homeJointNormFactorType R hR parameter) =
      MultiFormula.parameterProfile
        (normAddMultiStructure (E := XYSpace) R hR)
        normAddMultiFormula parameter := by
  funext row
  apply Subtype.ext
  exact euclidean_factor_normAddMultiFormula_value R hR row parameter

/-- Continuous Euclidean combination sends every jointly realizable factor
type to a local parameter type of the direct-sum norm formula. -/
def jointNormFactorTypeMap (R : ℝ) (hR : 0 < R) :
    JointNormFactorType R hR → XYNormLocalParameterType R hR := by
  intro type
  refine ⟨jointNormFactorProfile R hR type, ?_⟩
  have htype : type ∈
      closure (Set.range (homeJointNormFactorType R hR)) := by
    rw [(denseRange_homeJointNormFactorType R hR).closure_eq]
    exact Set.mem_univ type
  have hclosureImage : jointNormFactorProfile R hR type ∈
      closure (jointNormFactorProfile R hR ''
        Set.range (homeJointNormFactorType R hR)) :=
    image_closure_subset_closure_image
      (continuous_jointNormFactorProfile R hR) ⟨type, htype, rfl⟩
  apply closure_mono
    (s := jointNormFactorProfile R hR ''
      Set.range (homeJointNormFactorType R hR))
    (t := Set.range (MultiFormula.parameterProfile
      (normAddMultiStructure (E := XYSpace) R hR) normAddMultiFormula))
      ?_ hclosureImage
  rintro _ ⟨_, ⟨parameter, rfl⟩, rfl⟩
  exact ⟨parameter,
    (jointNormFactorProfile_homeJointNormFactorType R hR parameter).symm⟩

/-- The Euclidean combination map is continuous. -/
theorem continuous_jointNormFactorTypeMap (R : ℝ) (hR : 0 < R) :
    Continuous (jointNormFactorTypeMap R hR) := by
  apply continuous_induced_rng.2
  exact continuous_jointNormFactorProfile R hR

@[simp]
theorem jointNormFactorTypeMap_homeJointNormFactorType
    (R : ℝ) (hR : 0 < R)
    (parameter : PositiveNormBall XYSpace R) :
    jointNormFactorTypeMap R hR
        (homeJointNormFactorType R hR parameter) =
      MultiFormula.homeParameterType
        (normAddMultiStructure (E := XYSpace) R hR)
        normAddMultiFormula parameter := by
  apply Subtype.ext
  exact jointNormFactorProfile_homeJointNormFactorType R hR parameter

/-- Every direct-sum local parameter type is the Euclidean combination of a
jointly realizable pair of factor types. -/
theorem jointNormFactorTypeMap_surjective (R : ℝ) (hR : 0 < R) :
    Function.Surjective (jointNormFactorTypeMap R hR) := by
  let image : Set (XYNormLocalParameterType R hR) :=
    Set.range (jointNormFactorTypeMap R hR)
  have hclosed : IsClosed image := by
    exact (isCompact_range
      (continuous_jointNormFactorTypeMap R hR)).isClosed
  have hhome : Set.range (MultiFormula.homeParameterType
      (normAddMultiStructure (E := XYSpace) R hR) normAddMultiFormula) ⊆
      image := by
    rintro _ ⟨parameter, rfl⟩
    exact ⟨homeJointNormFactorType R hR parameter,
      jointNormFactorTypeMap_homeJointNormFactorType R hR parameter⟩
  have huniv : closure image = Set.univ := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← (MultiFormula.denseRange_homeParameterType
      (normAddMultiStructure (E := XYSpace) R hR)
      normAddMultiFormula).closure_eq]
    exact closure_mono hhome
  intro type
  have htype : type ∈ closure image := by
    rw [huniv]
    exact Set.mem_univ type
  have : type ∈ image := by
    rwa [hclosed.closure_eq] at htype
  exact this

end

end NormFormula.XY
