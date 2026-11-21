import NormFormula.Analytic.XHilbertEquiv
import NormFormula.ContinuousLogic.MultiPredicate
import NormFormula.ContinuousLogic.MultiReducedProduct
import NormFormula.ContinuousLogic.NormAdd
import NormFormula.ContinuousLogic.ScaledOrderViolation
import Mathlib.Tactic.DeriveEncodable

/-!
# The bounded norm--Hilbert expansion for `X`

On each positive norm ball of `XSpace`, this file names both normalized
translation predicates

* `‖x + y‖_X / (2R)`, and
* `‖x + y‖₂ / (2R)`.

It expresses the two quantitative comparisons from the paper's expanded
theory `T'` by universal zero-valued sentences and proves that equality of
complete expanded theories transfers the comparisons pointwise.

Besides the addition predicates used by the IP formula, the alphabet names
the row, parameter, and difference instances needed for the first finite
linear-combination fragment of `T'`.  These atoms support genuine
parallelogram and midpoint sentences in the next module.  Reconstructing an
actual Banach carrier still requires a subsequent coherent algebraic
expansion of the bounded language.
-/

namespace NormFormula.X.ContinuousLanguage

noncomputable section

open scoped Topology
open NormFormula.ContinuousLogic

universe u v

/-- The norm predicate and the auxiliary Hilbert predicate named in `T'`. -/
inductive ExpansionSymbol
  | norm
  | hilbert
  | normRow
  | normParameter
  | normSub
  | hilbertRow
  | hilbertParameter
  | hilbertSub
  deriving DecidableEq, Encodable

/-- Inclusion of the one-symbol norm-addition language into the expansion. -/
def includeNorm : NormAddSymbol → ExpansionSymbol
  | .norm => .norm

/-- Normalized auxiliary Hilbert-norm translation on a positive `XSpace`
ball. -/
def hilbertAddTruth (R : ℝ) (hR : 0 < R)
    (x y : PositiveNormBall XSpace R) : TruthValue := by
  refine ⟨‖toHilbert (x.1 + y.1)‖ / (2 * R),
    div_nonneg (norm_nonneg _) (by positivity), ?_⟩
  apply (div_le_one (by positivity : 0 < 2 * R)).2
  exact (norm_toHilbert_le (x.1 + y.1)).trans <|
    (norm_add_le x.1 y.1).trans (add_le_add x.2 y.2) |>.trans_eq (by ring)

@[simp]
theorem hilbertAddTruth_coe (R : ℝ) (hR : 0 < R)
    (x y : PositiveNormBall XSpace R) :
    (hilbertAddTruth R hR x y : ℝ) =
      ‖toHilbert (x.1 + y.1)‖ / (2 * R) :=
  rfl

/-- Uniform continuity of normalized auxiliary Hilbert-norm addition. -/
theorem hilbertAddTruth_uniformContinuous (R : ℝ) (hR : 0 < R) :
    UniformContinuous fun p :
        PositiveNormBall XSpace R × PositiveNormBall XSpace R ↦
      hilbertAddTruth R hR p.1 p.2 := by
  have hfst : UniformContinuous
      (fun p : PositiveNormBall XSpace R × PositiveNormBall XSpace R ↦
        (p.1.1 : XSpace)) :=
    uniformContinuous_subtype_val.comp uniformContinuous_fst
  have hsnd : UniformContinuous
      (fun p : PositiveNormBall XSpace R × PositiveNormBall XSpace R ↦
        (p.2.1 : XSpace)) :=
    uniformContinuous_subtype_val.comp uniformContinuous_snd
  have hhilbert : UniformContinuous
      (fun p : PositiveNormBall XSpace R × PositiveNormBall XSpace R ↦
        ‖toHilbert ((p.1.1 : XSpace) + (p.2.1 : XSpace))‖) :=
    uniformContinuous_norm.comp
      (continuousLinearEquivHilbertSum.toContinuousLinearMap.uniformContinuous.comp
        (hfst.add hsnd))
  exact (hhilbert.div_const' (2 * R)).subtype_mk _

/-- Normalized ambient norm of the row variable. -/
def normRowTruth (R : ℝ) (hR : 0 < R)
    (x _y : PositiveNormBall XSpace R) : TruthValue := by
  refine ⟨‖x.1‖ / R, div_nonneg (norm_nonneg _) hR.le, ?_⟩
  exact (div_le_one hR).2 x.2

/-- Normalized ambient norm of the parameter variable. -/
def normParameterTruth (R : ℝ) (hR : 0 < R)
    (_x y : PositiveNormBall XSpace R) : TruthValue := by
  refine ⟨‖y.1‖ / R, div_nonneg (norm_nonneg _) hR.le, ?_⟩
  exact (div_le_one hR).2 y.2

/-- Normalized ambient norm of the difference of the two variables. -/
def normSubTruth (R : ℝ) (hR : 0 < R)
    (x y : PositiveNormBall XSpace R) : TruthValue := by
  refine ⟨‖x.1 - y.1‖ / (2 * R),
    div_nonneg (norm_nonneg _) (by positivity), ?_⟩
  apply (div_le_one (by positivity : 0 < 2 * R)).2
  exact (norm_sub_le x.1 y.1).trans
    ((add_le_add x.2 y.2).trans_eq (by ring))

/-- Normalized auxiliary Hilbert norm of the row variable. -/
def hilbertRowTruth (R : ℝ) (hR : 0 < R)
    (x _y : PositiveNormBall XSpace R) : TruthValue := by
  refine ⟨‖toHilbert x.1‖ / R, div_nonneg (norm_nonneg _) hR.le, ?_⟩
  exact (div_le_one hR).2 ((norm_toHilbert_le x.1).trans x.2)

/-- Normalized auxiliary Hilbert norm of the parameter variable. -/
def hilbertParameterTruth (R : ℝ) (hR : 0 < R)
    (_x y : PositiveNormBall XSpace R) : TruthValue := by
  refine ⟨‖toHilbert y.1‖ / R, div_nonneg (norm_nonneg _) hR.le, ?_⟩
  exact (div_le_one hR).2 ((norm_toHilbert_le y.1).trans y.2)

/-- Normalized auxiliary Hilbert norm of the difference of the variables. -/
def hilbertSubTruth (R : ℝ) (hR : 0 < R)
    (x y : PositiveNormBall XSpace R) : TruthValue := by
  refine ⟨‖toHilbert (x.1 - y.1)‖ / (2 * R),
    div_nonneg (norm_nonneg _) (by positivity), ?_⟩
  apply (div_le_one (by positivity : 0 < 2 * R)).2
  exact (norm_toHilbert_le (x.1 - y.1)).trans <|
    (norm_sub_le x.1 y.1).trans
      ((add_le_add x.2 y.2).trans_eq (by ring))

/-- Uniform continuity of the six additional basic linear-combination
predicates. -/
theorem basicCombinationTruth_uniformContinuous
    (R : ℝ) (hR : 0 < R) (symbol : ExpansionSymbol) :
    UniformContinuous fun p :
        PositiveNormBall XSpace R × PositiveNormBall XSpace R ↦
      match symbol with
      | .norm => normAddTruth R hR p.1 p.2
      | .hilbert => hilbertAddTruth R hR p.1 p.2
      | .normRow => normRowTruth R hR p.1 p.2
      | .normParameter => normParameterTruth R hR p.1 p.2
      | .normSub => normSubTruth R hR p.1 p.2
      | .hilbertRow => hilbertRowTruth R hR p.1 p.2
      | .hilbertParameter => hilbertParameterTruth R hR p.1 p.2
      | .hilbertSub => hilbertSubTruth R hR p.1 p.2 := by
  have hfst : UniformContinuous
      (fun p : PositiveNormBall XSpace R × PositiveNormBall XSpace R ↦
        (p.1.1 : XSpace)) :=
    uniformContinuous_subtype_val.comp uniformContinuous_fst
  have hsnd : UniformContinuous
      (fun p : PositiveNormBall XSpace R × PositiveNormBall XSpace R ↦
        (p.2.1 : XSpace)) :=
    uniformContinuous_subtype_val.comp uniformContinuous_snd
  have hhilbert : UniformContinuous (fun z : XSpace ↦ toHilbert z) :=
    continuousLinearEquivHilbertSum.toContinuousLinearMap.uniformContinuous
  cases symbol with
  | norm => exact normAddTruth_uniformContinuous R hR
  | hilbert => exact hilbertAddTruth_uniformContinuous R hR
  | normRow =>
      exact ((uniformContinuous_norm.comp hfst).div_const' R).subtype_mk _
  | normParameter =>
      exact ((uniformContinuous_norm.comp hsnd).div_const' R).subtype_mk _
  | normSub =>
      exact ((uniformContinuous_norm.comp (hfst.sub hsnd)).div_const'
        (2 * R)).subtype_mk _
  | hilbertRow =>
      exact ((uniformContinuous_norm.comp (hhilbert.comp hfst)).div_const'
        R).subtype_mk _
  | hilbertParameter =>
      exact ((uniformContinuous_norm.comp (hhilbert.comp hsnd)).div_const'
        R).subtype_mk _
  | hilbertSub =>
      exact ((uniformContinuous_norm.comp (hhilbert.comp (hfst.sub hsnd))).div_const'
        (2 * R)).subtype_mk _

/-- The two-predicate comparison fragment of the bounded `XSpace`
expansion. -/
def expansionStructure (R : ℝ) (hR : 0 < R) :
    MultiStructure ExpansionSymbol where
  Row := PositiveNormBall XSpace R
  Parameter := PositiveNormBall XSpace R
  rowNonempty := ⟨⟨0, by simpa using hR.le⟩⟩
  parameterNonempty := ⟨⟨0, by simpa using hR.le⟩⟩
  predicate
    | .norm => normAddTruth R hR
    | .hilbert => hilbertAddTruth R hR
    | .normRow => normRowTruth R hR
    | .normParameter => normParameterTruth R hR
    | .normSub => normSubTruth R hR
    | .hilbertRow => hilbertRowTruth R hR
    | .hilbertParameter => hilbertParameterTruth R hR
    | .hilbertSub => hilbertSubTruth R hR
  predicate_uniformContinuous := by
    intro symbol
    cases symbol with
    | norm => exact normAddTruth_uniformContinuous R hR
    | hilbert => exact hilbertAddTruth_uniformContinuous R hR
    | normRow =>
        exact basicCombinationTruth_uniformContinuous R hR .normRow
    | normParameter =>
        exact basicCombinationTruth_uniformContinuous R hR .normParameter
    | normSub =>
        exact basicCombinationTruth_uniformContinuous R hR .normSub
    | hilbertRow =>
        exact basicCombinationTruth_uniformContinuous R hR .hilbertRow
    | hilbertParameter =>
        exact basicCombinationTruth_uniformContinuous R hR .hilbertParameter
    | hilbertSub =>
        exact basicCombinationTruth_uniformContinuous R hR .hilbertSub

/-- The expansion inherits the usual positive-ball metric bounds. -/
def expansionStructureBounds (R : ℝ) (hR : 0 < R) :
    (expansionStructure R hR).Bounds where
  row := (normAddStructureBounds (E := XSpace) R hR).row
  parameter := (normAddStructureBounds (E := XSpace) R hR).parameter

/-- The normalized ambient norm-addition formula. -/
def normFormula : MultiFormula ExpansionSymbol 1 1 :=
  .predicate .norm 0 0

/-- The normalized auxiliary Hilbert norm-addition formula. -/
def hilbertFormula : MultiFormula ExpansionSymbol 1 1 :=
  .predicate .hilbert 0 0

/-- Failure of the lower comparison `h(z) ≤ ‖z‖_X`. -/
def hilbertLeNormViolationFormula : MultiFormula ExpansionSymbol 1 1 :=
  .connective (scaledOrderViolationConnective 1 (by norm_num))
    ![hilbertFormula, normFormula]

/-- Failure of the upper comparison `‖z‖_X ≤ √3 h(z)`. -/
def normLeSqrtThreeHilbertViolationFormula :
    MultiFormula ExpansionSymbol 1 1 :=
  .connective
    (scaledOrderViolationConnective (Real.sqrt 3) (Real.sqrt_nonneg 3))
    ![normFormula, hilbertFormula]

/-- Universal closure of a binary comparison formula. -/
def universalBinarySentence (φ : MultiFormula ExpansionSymbol 1 1) :
    MultiSentence ExpansionSymbol :=
  .iSupParameter (.iSupRow φ)

/-- The universal lower-comparison sentence. -/
def hilbertLeNormSentence : MultiSentence ExpansionSymbol :=
  universalBinarySentence hilbertLeNormViolationFormula

/-- The universal upper-comparison sentence. -/
def normLeSqrtThreeHilbertSentence : MultiSentence ExpansionSymbol :=
  universalBinarySentence normLeSqrtThreeHilbertViolationFormula

@[simp]
theorem normFormula_value (R : ℝ) (hR : 0 < R)
    (x y : PositiveNormBall XSpace R) :
    normFormula.binaryValue (expansionStructure R hR) x y =
      ‖x.1 + y.1‖ / (2 * R) :=
  rfl

@[simp]
theorem hilbertFormula_value (R : ℝ) (hR : 0 < R)
    (x y : PositiveNormBall XSpace R) :
    hilbertFormula.binaryValue (expansionStructure R hR) x y =
      ‖toHilbert (x.1 + y.1)‖ / (2 * R) :=
  rfl

/-- The concrete expansion satisfies the lower comparison pointwise. -/
theorem hilbertFormula_le_normFormula (R : ℝ) (hR : 0 < R)
    (x y : PositiveNormBall XSpace R) :
    hilbertFormula.binaryValue (expansionStructure R hR) x y ≤
      normFormula.binaryValue (expansionStructure R hR) x y := by
  exact div_le_div_of_nonneg_right (norm_toHilbert_le (x.1 + y.1))
    (by positivity)

/-- The concrete expansion satisfies the upper comparison pointwise. -/
theorem normFormula_le_sqrtThree_mul_hilbertFormula
    (R : ℝ) (hR : 0 < R)
    (x y : PositiveNormBall XSpace R) :
    normFormula.binaryValue (expansionStructure R hR) x y ≤
      Real.sqrt 3 *
        hilbertFormula.binaryValue (expansionStructure R hR) x y := by
  have hcomparison := norm_ofHilbert_le (toHilbert (x.1 + y.1))
  have hdenom : 0 ≤ 2 * R := by positivity
  have hxy : ‖x.1 + y.1‖ ≤
      Real.sqrt 3 * ‖toHilbert (x.1 + y.1)‖ := by
    simpa using hcomparison
  calc
    ‖x.1 + y.1‖ / (2 * R) ≤
        (Real.sqrt 3 * ‖toHilbert (x.1 + y.1)‖) / (2 * R) :=
      div_le_div_of_nonneg_right hxy hdenom
    _ = Real.sqrt 3 *
        (‖toHilbert (x.1 + y.1)‖ / (2 * R)) := by ring

/-- Both comparison-violation formulae vanish in the concrete expansion. -/
theorem comparisonViolationFormulae_realize
    (R : ℝ) (hR : 0 < R)
    (rows : Fin 1 → PositiveNormBall XSpace R)
    (parameters : Fin 1 → PositiveNormBall XSpace R) :
    hilbertLeNormViolationFormula.realize
        (expansionStructure R hR) rows parameters = zeroTruthValue ∧
      normLeSqrtThreeHilbertViolationFormula.realize
        (expansionStructure R hR) rows parameters = zeroTruthValue := by
  constructor
  · apply (scaledOrderViolationConnective_eq_zero_iff 1 (by norm_num) _).2
    simpa using hilbertFormula_le_normFormula R hR (rows 0) (parameters 0)
  · apply (scaledOrderViolationConnective_eq_zero_iff
      (Real.sqrt 3) (Real.sqrt_nonneg 3) _).2
    simpa using normFormula_le_sqrtThree_mul_hilbertFormula
      R hR (rows 0) (parameters 0)

/-- A universally closed binary formula has value zero when all its instances
vanish. -/
theorem universalBinarySentence_value_eq_zero
    (R : ℝ) (hR : 0 < R) (φ : MultiFormula ExpansionSymbol 1 1)
    (hφ : ∀ (rows : Fin 1 → PositiveNormBall XSpace R)
      (parameters : Fin 1 → PositiveNormBall XSpace R),
      φ.realize (expansionStructure R hR) rows parameters = zeroTruthValue) :
    (universalBinarySentence φ).value (expansionStructure R hR) =
      zeroTruthValue := by
  change (⨆ parameter : PositiveNormBall XSpace R,
      ⨆ row : PositiveNormBall XSpace R,
        φ.realize (expansionStructure R hR)
          (Fin.cons row Fin.elim0) (Fin.cons parameter Fin.elim0)) =
    zeroTruthValue
  apply le_antisymm
  · refine iSup_le fun parameter ↦ iSup_le fun row ↦ ?_
    exact (hφ (Fin.cons row Fin.elim0)
      (Fin.cons parameter Fin.elim0)).le
  · exact ((⨆ parameter : PositiveNormBall XSpace R,
      ⨆ row : PositiveNormBall XSpace R,
        φ.realize (expansionStructure R hR)
          (Fin.cons row Fin.elim0) (Fin.cons parameter Fin.elim0)) :
      TruthValue).2.1

@[simp]
theorem hilbertLeNormSentence_value (R : ℝ) (hR : 0 < R) :
    hilbertLeNormSentence.value (expansionStructure R hR) =
      zeroTruthValue :=
  universalBinarySentence_value_eq_zero R hR _ fun rows parameters ↦
    (comparisonViolationFormulae_realize R hR rows parameters).1

@[simp]
theorem normLeSqrtThreeHilbertSentence_value (R : ℝ) (hR : 0 < R) :
    normLeSqrtThreeHilbertSentence.value (expansionStructure R hR) =
      zeroTruthValue :=
  universalBinarySentence_value_eq_zero R hR _ fun rows parameters ↦
    (comparisonViolationFormulae_realize R hR rows parameters).2

/-- Every instance of a binary formula is bounded by its universal closure. -/
theorem realize_le_universalBinarySentence
    (N : MultiStructure.{u, v} ExpansionSymbol)
    (φ : MultiFormula ExpansionSymbol 1 1)
    (rows : Fin 1 → N.Row) (parameters : Fin 1 → N.Parameter) :
    φ.realize N rows parameters ≤ (universalBinarySentence φ).value N := by
  have hrows : rows = Fin.cons (rows 0) Fin.elim0 := by
    funext i
    fin_cases i
    rfl
  have hparameters : parameters = Fin.cons (parameters 0) Fin.elim0 := by
    funext i
    fin_cases i
    rfl
  rw [hrows, hparameters]
  refine le_iSup_of_le (parameters 0) ?_
  exact le_iSup
    (fun row : N.Row ↦ φ.realize N (Fin.cons row Fin.elim0)
      (Fin.cons (parameters 0) Fin.elim0)) (rows 0)

/-- Equality with the complete theory of the concrete expansion transfers
both Hilbert comparison inequalities to every assignment. -/
theorem comparisons_of_sameCompleteTheory
    (R : ℝ) (hR : 0 < R)
    (N : MultiStructure.{u, v} ExpansionSymbol)
    (hTheory : MultiSameCompleteTheory (expansionStructure R hR) N)
    (rows : Fin 1 → N.Row) (parameters : Fin 1 → N.Parameter) :
    (hilbertFormula.realize N rows parameters : ℝ) ≤
        (normFormula.realize N rows parameters : ℝ) ∧
      (normFormula.realize N rows parameters : ℝ) ≤
        Real.sqrt 3 * (hilbertFormula.realize N rows parameters : ℝ) := by
  have hlowerSentence : hilbertLeNormSentence.value N = zeroTruthValue := by
    calc
      hilbertLeNormSentence.value N =
          hilbertLeNormSentence.value (expansionStructure R hR) :=
        (hTheory hilbertLeNormSentence).symm
      _ = zeroTruthValue := hilbertLeNormSentence_value R hR
  have hupperSentence : normLeSqrtThreeHilbertSentence.value N =
      zeroTruthValue := by
    calc
      normLeSqrtThreeHilbertSentence.value N =
          normLeSqrtThreeHilbertSentence.value (expansionStructure R hR) :=
        (hTheory normLeSqrtThreeHilbertSentence).symm
      _ = zeroTruthValue := normLeSqrtThreeHilbertSentence_value R hR
  constructor
  · have hle := realize_le_universalBinarySentence N
      hilbertLeNormViolationFormula rows parameters
    change hilbertLeNormViolationFormula.realize N rows parameters ≤
      hilbertLeNormSentence.value N at hle
    rw [hlowerSentence] at hle
    have hzero : hilbertLeNormViolationFormula.realize N rows parameters =
        zeroTruthValue := le_antisymm hle
          (hilbertLeNormViolationFormula.realize N rows parameters).2.1
    simpa using
      (scaledOrderViolationConnective_eq_zero_iff 1 (by norm_num) _).1 hzero
  · have hle := realize_le_universalBinarySentence N
      normLeSqrtThreeHilbertViolationFormula rows parameters
    change normLeSqrtThreeHilbertViolationFormula.realize N rows parameters ≤
      normLeSqrtThreeHilbertSentence.value N at hle
    rw [hupperSentence] at hle
    have hzero : normLeSqrtThreeHilbertViolationFormula.realize N rows parameters =
        zeroTruthValue := le_antisymm hle
          (normLeSqrtThreeHilbertViolationFormula.realize N rows parameters).2.1
    simpa using (scaledOrderViolationConnective_eq_zero_iff
      (Real.sqrt 3) (Real.sqrt_nonneg 3) _).1 hzero

end

end NormFormula.X.ContinuousLanguage
