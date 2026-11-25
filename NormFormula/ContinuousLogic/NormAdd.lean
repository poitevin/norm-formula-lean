import NormFormula.ContinuousLogic.Compactness
import NormFormula.ContinuousLogic.MultiPredicate
import Mathlib.Tactic.DeriveEncodable

/-!
# The bounded norm-addition predicate

This file interprets the minimal continuous language on a positive closed
norm ball.  The atomic predicate is `‖x + y‖ / (2R)`, hence `[0,1]`-valued and
uniformly continuous.  It then assembles all positive ball radii into the
semantic statement that the norm formula has IP in its complete theory.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open scoped Topology

/-- A positive closed norm ball, used as one bounded continuous-logic sort. -/
abbrev PositiveNormBall (E : Type*) [Norm E] (R : ℝ) :=
  NormFormula.ClosedNormBall E R

variable {E : Type*} [NormedAddCommGroup E]

/-- Normalized norm addition on the positive `R`-ball. -/
def normAddTruth (R : ℝ) (hR : 0 < R)
    (x y : PositiveNormBall E R) : TruthValue := by
  refine ⟨‖x.1 + y.1‖ / (2 * R), div_nonneg (norm_nonneg _) (by positivity), ?_⟩
  apply (div_le_one (by positivity : 0 < 2 * R)).2
  calc
    ‖x.1 + y.1‖ ≤ ‖x.1‖ + ‖y.1‖ := norm_add_le _ _
    _ ≤ R + R := add_le_add x.2 y.2
    _ = 2 * R := by ring


/-- Uniform continuity of normalized norm addition. -/
theorem normAddTruth_uniformContinuous (R : ℝ) (hR : 0 < R) :
    UniformContinuous fun p : PositiveNormBall E R × PositiveNormBall E R ↦
      normAddTruth R hR p.1 p.2 := by
  have hfst : UniformContinuous
      (fun p : PositiveNormBall E R × PositiveNormBall E R ↦ (p.1.1 : E)) :=
    uniformContinuous_subtype_val.comp uniformContinuous_fst
  have hsnd : UniformContinuous
      (fun p : PositiveNormBall E R × PositiveNormBall E R ↦ (p.2.1 : E)) :=
    uniformContinuous_subtype_val.comp uniformContinuous_snd
  have hnorm : UniformContinuous
      (fun p : PositiveNormBall E R × PositiveNormBall E R ↦
        ‖(p.1.1 : E) + (p.2.1 : E)‖) :=
    uniformContinuous_norm.comp (hfst.add hsnd)
  exact (hnorm.div_const' (2 * R)).subtype_mk _

/-- The bounded two-sorted structure carried by one positive norm ball.  The
two sorts happen to have the same carrier, but remain syntactically distinct. -/
def normAddStructure (R : ℝ) (hR : 0 < R) : Structure where
  Row := PositiveNormBall E R
  Parameter := PositiveNormBall E R
  rowNonempty := ⟨⟨0, by simpa using hR.le⟩⟩
  parameterNonempty := ⟨⟨0, by simpa using hR.le⟩⟩
  predicate := normAddTruth R hR
  predicate_uniformContinuous := normAddTruth_uniformContinuous R hR


/-- The one-symbol language used for normalized norm addition on arbitrary
positive norm balls. -/
inductive NormAddSymbol
  | norm
  deriving DecidableEq, Encodable

/-- The many-predicate presentation of a positive norm ball.  This is the
generic one-symbol counterpart of `normAddStructure`, used by local type
spaces and by the later direct-sum maps. -/
def normAddMultiStructure (R : ℝ) (hR : 0 < R) :
    MultiStructure NormAddSymbol where
  Row := PositiveNormBall E R
  Parameter := PositiveNormBall E R
  rowNonempty := ⟨⟨0, by simpa using hR.le⟩⟩
  parameterNonempty := ⟨⟨0, by simpa using hR.le⟩⟩
  predicate
    | .norm => normAddTruth R hR
  predicate_uniformContinuous := by
    intro symbol
    cases symbol
    exact normAddTruth_uniformContinuous R hR

/-- The atomic norm formula in the generic one-symbol many-predicate
language. -/
def normAddMultiFormula : MultiFormula NormAddSymbol 1 1 :=
  .predicate .norm 0 0

@[simp]
theorem normAddMultiFormula_value (R : ℝ) (hR : 0 < R)
    (x y : PositiveNormBall E R) :
    normAddMultiFormula.binaryValue
        (normAddMultiStructure (E := E) R hR) x y =
      ‖x.1 + y.1‖ / (2 * R) :=
  rfl

/-- Both positive norm-ball sorts have diameter at most `2R`, the same scale
used to normalize the atomic norm-addition predicate. -/
def normAddStructureBounds (R : ℝ) (hR : 0 < R) :
    (normAddStructure (E := E) R hR).Bounds := by
  let ballBound : BoundedMetricSort (PositiveNormBall E R) :=
    { scale := 2 * R
      scale_pos := by positivity
      dist_le_scale := by
        intro x y
        rw [Subtype.dist_eq, dist_eq_norm]
        calc
          ‖x.1 - y.1‖ ≤ ‖x.1‖ + ‖y.1‖ := norm_sub_le _ _
          _ ≤ R + R := add_le_add x.2 y.2
          _ = 2 * R := by ring }
  exact ⟨ballBound, ballBound⟩

/-- Continuous compactness for every positive ball sort of a normed additive
group. -/
def NormAddCompactness (E : Type*) [NormedAddCommGroup E] : Prop :=
  ∀ (R : ℝ) (hR : 0 < R),
    AtomicFinitePatternCompactness (normAddStructure (E := E) R hR)

/-- The metric-ultrapower construction discharges norm-addition compactness
for every normed additive commutative group. -/
theorem normAddCompactness : NormAddCompactness E := by
  intro R hR
  exact atomicFinitePatternCompactness_of_bounds
    (normAddStructure (E := E) R hR) (normAddStructureBounds R hR)

/-- The semantic statement that the norm formula has IP in the complete
theory of at least one positive ball sort. -/
def NormFormulaHasIPInCompleteTheory
    (E : Type*) [NormedAddCommGroup E] : Prop :=
  ∃ (R : ℝ) (hR : 0 < R),
    HasIPInCompleteTheory (normAddStructure (E := E) R hR) Formula.atomic

/-- Raw bounded fixed-gap norm patterns give finite patterns for the normalized
atomic predicate on one sufficiently large positive ball. -/
theorem normAdd_hasFinitePatterns_of_raw_patterns
    (R_x R_y low high : ℝ)
    (hpatterns : HasIPPatternsInEveryDimension
      (fun x y : E ↦ ‖x + y‖) R_x R_y low high) :
    let R := 1 + |R_x| + |R_y|
    HasFiniteIPPatternsInEveryDimension
      (normAddStructure (E := E) R (by positivity)) Formula.atomic
      (low / (2 * R)) (high / (2 * R)) := by
  dsimp only
  let R := 1 + |R_x| + |R_y|
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hxR : R_x ≤ R := by
    dsimp [R]
    linarith [le_abs_self R_x, abs_nonneg R_y]
  have hyR : R_y ≤ R := by
    dsimp [R]
    linarith [le_abs_self R_y, abs_nonneg R_x]
  intro n
  obtain ⟨rows, hrows, hip⟩ := hpatterns n
  let boundedRows : Fin n → PositiveNormBall E R :=
    fun i ↦ ⟨rows i, (hrows i).trans hxR⟩
  refine ⟨boundedRows, ?_⟩
  intro subset
  obtain ⟨parameter, hin, hout⟩ := hip subset
  let boundedParameter : PositiveNormBall E R :=
    ⟨parameter.1, parameter.2.trans hyR⟩
  refine ⟨boundedParameter, ?_, ?_⟩
  · intro i hi
    change high / (2 * R) ≤ ‖rows i + parameter.1‖ / (2 * R)
    exact (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * R)).2
      (hin i hi)
  · intro i hi
    change ‖rows i + parameter.1‖ / (2 * R) ≤ low / (2 * R)
    exact (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * R)).2
      (hout i hi)

/-- The compactness family turns raw fixed-gap norm patterns into semantic IP
in the complete bounded theory. -/
theorem normFormula_hasIPInCompleteTheory_of_patterns
    (R_x R_y low high : ℝ) (hgap : low < high)
    (hpatterns : HasIPPatternsInEveryDimension
      (fun x y : E ↦ ‖x + y‖) R_x R_y low high) :
    NormFormulaHasIPInCompleteTheory E := by
  let R := 1 + |R_x| + |R_y|
  have hR : 0 < R := by
    dsimp [R]
    positivity
  refine ⟨R, hR, ?_⟩
  apply normAddCompactness R hR (low / (2 * R)) (high / (2 * R))
  · exact (div_lt_div_iff_of_pos_right (by positivity : 0 < 2 * R)).2 hgap
  · simpa [R] using normAdd_hasFinitePatterns_of_raw_patterns
      R_x R_y low high hpatterns

/-- The minimal continuous syntax and semantic theory notion instantiate the
paper's former syntax-free compactness interface for the norm formula. -/
def normCompleteTheoryIPSemantics
    (E : Type*) [NormedAddCommGroup E] :
    NormFormula.CompleteTheoryIPSemantics E E where
  Formula := Unit
  formulaValue := fun _ x y ↦ ‖x + y‖
  IsIPInTheory := fun _ ↦ NormFormulaHasIPInCompleteTheory E
  finitePatternsToTheoryIP := by
    intro _ R_x R_y low high hgap hpatterns
    exact normFormula_hasIPInCompleteTheory_of_patterns
      R_x R_y low high hgap hpatterns

end

end NormFormula.ContinuousLogic
