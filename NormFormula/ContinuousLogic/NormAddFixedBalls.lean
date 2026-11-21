import NormFormula.ContinuousLogic.XLocalTypeNIP
import NormFormula.ContinuousLogic.XYLocalTypeNIP
import NormFormula.ContinuousLogic.YLocalTypeNIP
import NormFormula.ModelTheory.SeparableIPModel

/-!
# Independent row and parameter balls for norm addition

The generic norm-addition structure used earlier gives both variables one
common positive radius.  The standard Banach language permits the row and
parameter variables to belong to independently fixed balls.  This file gives
that restriction an explicit structure, embeds it into one common positive
ball, records the exact threshold normalization, and handles radius zero.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open scoped Topology

universe u

variable {E : Type u} [NormedAddCommGroup E]

/-- A strictly positive common radius containing nonnegative row and
parameter balls of radii `Rₓ` and `Rᵧ`. -/
def fixedBallCommonRadius (Rₓ Rᵧ : ℝ) : ℝ :=
  1 + Rₓ + Rᵧ

theorem fixedBallCommonRadius_pos {Rₓ Rᵧ : ℝ}
    (hRₓ : 0 ≤ Rₓ) (hRᵧ : 0 ≤ Rᵧ) :
    0 < fixedBallCommonRadius Rₓ Rᵧ := by
  unfold fixedBallCommonRadius
  linarith

theorem rowRadius_le_fixedBallCommonRadius {Rₓ Rᵧ : ℝ}
    (hRᵧ : 0 ≤ Rᵧ) :
    Rₓ ≤ fixedBallCommonRadius Rₓ Rᵧ := by
  unfold fixedBallCommonRadius
  linarith

theorem parameterRadius_le_fixedBallCommonRadius {Rₓ Rᵧ : ℝ}
    (hRₓ : 0 ≤ Rₓ) :
    Rᵧ ≤ fixedBallCommonRadius Rₓ Rᵧ := by
  unfold fixedBallCommonRadius
  linarith

/-- Inclusion of the independently bounded row sort into the common ball. -/
def fixedRowToCommonBall (Rₓ Rᵧ : ℝ) (hRᵧ : 0 ≤ Rᵧ) :
    ClosedNormBall E Rₓ → PositiveNormBall E (fixedBallCommonRadius Rₓ Rᵧ) :=
  fun x ↦ ⟨x.1, x.2.trans (rowRadius_le_fixedBallCommonRadius hRᵧ)⟩

/-- Inclusion of the independently bounded parameter sort into the common
ball. -/
def fixedParameterToCommonBall (Rₓ Rᵧ : ℝ) (hRₓ : 0 ≤ Rₓ) :
    ClosedNormBall E Rᵧ → PositiveNormBall E (fixedBallCommonRadius Rₓ Rᵧ) :=
  fun y ↦ ⟨y.1, y.2.trans (parameterRadius_le_fixedBallCommonRadius hRₓ)⟩

theorem fixedRowToCommonBall_uniformContinuous
    (Rₓ Rᵧ : ℝ) (hRᵧ : 0 ≤ Rᵧ) :
    UniformContinuous (fixedRowToCommonBall (E := E) Rₓ Rᵧ hRᵧ) :=
  uniformContinuous_subtype_val.subtype_mk _

theorem fixedParameterToCommonBall_uniformContinuous
    (Rₓ Rᵧ : ℝ) (hRₓ : 0 ≤ Rₓ) :
    UniformContinuous
      (fixedParameterToCommonBall (E := E) Rₓ Rᵧ hRₓ) :=
  uniformContinuous_subtype_val.subtype_mk _

/-- Norm addition on independent fixed balls, normalized by twice the chosen
common radius.  This is exactly the restriction of the existing equal-ball
predicate. -/
def fixedNormAddTruth
    (Rₓ Rᵧ : ℝ) (hRₓ : 0 ≤ Rₓ) (hRᵧ : 0 ≤ Rᵧ)
    (x : ClosedNormBall E Rₓ) (y : ClosedNormBall E Rᵧ) : TruthValue :=
  normAddTruth (fixedBallCommonRadius Rₓ Rᵧ)
    (fixedBallCommonRadius_pos hRₓ hRᵧ)
    (fixedRowToCommonBall Rₓ Rᵧ hRᵧ x)
    (fixedParameterToCommonBall Rₓ Rᵧ hRₓ y)

@[simp] theorem fixedNormAddTruth_coe
    (Rₓ Rᵧ : ℝ) (hRₓ : 0 ≤ Rₓ) (hRᵧ : 0 ≤ Rᵧ)
    (x : ClosedNormBall E Rₓ) (y : ClosedNormBall E Rᵧ) :
    (fixedNormAddTruth Rₓ Rᵧ hRₓ hRᵧ x y : ℝ) =
      ‖x.1 + y.1‖ / (2 * fixedBallCommonRadius Rₓ Rᵧ) :=
  rfl

set_option maxHeartbeats 800000 in
theorem fixedNormAddTruth_uniformContinuous
    (Rₓ Rᵧ : ℝ) (hRₓ : 0 ≤ Rₓ) (hRᵧ : 0 ≤ Rᵧ) :
    UniformContinuous fun p :
        ClosedNormBall E Rₓ × ClosedNormBall E Rᵧ ↦
      fixedNormAddTruth Rₓ Rᵧ hRₓ hRᵧ p.1 p.2 := by
  have hrow : UniformContinuous fun p :
      ClosedNormBall E Rₓ × ClosedNormBall E Rᵧ ↦
        fixedRowToCommonBall Rₓ Rᵧ hRᵧ p.1 :=
    (fixedRowToCommonBall_uniformContinuous Rₓ Rᵧ hRᵧ).comp
      uniformContinuous_fst
  have hparameter : UniformContinuous fun p :
      ClosedNormBall E Rₓ × ClosedNormBall E Rᵧ ↦
        fixedParameterToCommonBall Rₓ Rᵧ hRₓ p.2 :=
    (fixedParameterToCommonBall_uniformContinuous Rₓ Rᵧ hRₓ).comp
      uniformContinuous_snd
  exact (normAddTruth_uniformContinuous
    (E := E) (fixedBallCommonRadius Rₓ Rᵧ)
      (fixedBallCommonRadius_pos hRₓ hRᵧ)).comp
        (hrow.prodMk hparameter)

/-- The one-symbol structure with independent row and parameter radii. -/
def normAddFixedMultiStructure
    (Rₓ Rᵧ : ℝ) (hRₓ : 0 ≤ Rₓ) (hRᵧ : 0 ≤ Rᵧ) :
    MultiStructure NormAddSymbol where
  Row := ClosedNormBall E Rₓ
  Parameter := ClosedNormBall E Rᵧ
  rowNonempty := ⟨⟨0, by simpa using hRₓ⟩⟩
  parameterNonempty := ⟨⟨0, by simpa using hRᵧ⟩⟩
  predicate
    | .norm => fixedNormAddTruth Rₓ Rᵧ hRₓ hRᵧ
  predicate_uniformContinuous := by
    intro symbol
    cases symbol
    exact fixedNormAddTruth_uniformContinuous Rₓ Rᵧ hRₓ hRᵧ

@[simp] theorem normAddFixedMultiFormula_value
    (Rₓ Rᵧ : ℝ) (hRₓ : 0 ≤ Rₓ) (hRᵧ : 0 ≤ Rᵧ)
    (x : ClosedNormBall E Rₓ) (y : ClosedNormBall E Rᵧ) :
    normAddMultiFormula.binaryValue
        (normAddFixedMultiStructure (E := E) Rₓ Rᵧ hRₓ hRᵧ) x y =
      ‖x.1 + y.1‖ / (2 * fixedBallCommonRadius Rₓ Rᵧ) :=
  rfl

/-- A fixed-ball infinite witness embeds into the common equal-radius
structure with unchanged normalized thresholds. -/
theorem fixed_hasInfiniteIPWitness_to_common
    (Rₓ Rᵧ : ℝ) (hRₓ : 0 ≤ Rₓ) (hRᵧ : 0 ≤ Rᵧ)
    {low high : ℝ}
    (hIP : MultiFormula.HasInfiniteIPWitness
      (normAddFixedMultiStructure (E := E) Rₓ Rᵧ hRₓ hRᵧ)
      normAddMultiFormula low high) :
    MultiFormula.HasInfiniteIPWitness
      (normAddMultiStructure (E := E) (fixedBallCommonRadius Rₓ Rᵧ)
        (fixedBallCommonRadius_pos hRₓ hRᵧ))
      normAddMultiFormula low high := by
  obtain ⟨rows, hrows⟩ := hIP
  refine ⟨fun i ↦ fixedRowToCommonBall Rₓ Rᵧ hRᵧ (rows i), ?_⟩
  intro A B hdisjoint
  obtain ⟨parameter, hlow, hhigh⟩ := hrows A B hdisjoint
  refine ⟨fixedParameterToCommonBall Rₓ Rᵧ hRₓ parameter, ?_, ?_⟩
  · intro i hi
    simpa using hlow i hi
  · intro i hi
    simpa using hhigh i hi

/-- NIP on the common positive ball implies NIP for independently fixed
nonnegative row and parameter radii. -/
theorem normAddFixedMultiFormula_isNIPOnStructure_of_common
    (Rₓ Rᵧ : ℝ) (hRₓ : 0 ≤ Rₓ) (hRᵧ : 0 ≤ Rᵧ)
    (hcommon : MultiFormula.IsNIPOnStructure
      (normAddMultiStructure (E := E) (fixedBallCommonRadius Rₓ Rᵧ)
        (fixedBallCommonRadius_pos hRₓ hRᵧ)) normAddMultiFormula) :
    MultiFormula.IsNIPOnStructure
      (normAddFixedMultiStructure (E := E) Rₓ Rᵧ hRₓ hRᵧ)
      normAddMultiFormula := by
  intro hfixed
  apply hcommon
  obtain ⟨low, high, hgap, hIP⟩ := hfixed
  exact ⟨low, high, hgap,
    fixed_hasInfiniteIPWitness_to_common Rₓ Rᵧ hRₓ hRᵧ hIP⟩

/-- Raw witnesses on independent balls acquire exactly the displayed common
normalization. -/
theorem hasInfiniteIPWitness_fixed_of_bounded
    (Rₓ Rᵧ low high : ℝ) (hRₓ : 0 ≤ Rₓ) (hRᵧ : 0 ≤ Rᵧ)
    (hIP : NormFormula.HasBoundedInfiniteIPWitness
      (fun x y : E ↦ ‖x + y‖) Rₓ Rᵧ low high) :
    MultiFormula.HasInfiniteIPWitness
      (normAddFixedMultiStructure (E := E) Rₓ Rᵧ hRₓ hRᵧ)
      normAddMultiFormula
      (low / (2 * fixedBallCommonRadius Rₓ Rᵧ))
      (high / (2 * fixedBallCommonRadius Rₓ Rᵧ)) := by
  obtain ⟨rows, hrowBound, hrows⟩ := hIP
  refine ⟨fun i ↦ ⟨rows i, hrowBound i⟩, ?_⟩
  intro A B hdisjoint
  obtain ⟨parameter, hparameterBound, hlow, hhigh⟩ :=
    hrows A B hdisjoint
  refine ⟨⟨parameter, hparameterBound⟩, ?_, ?_⟩
  · intro i hi
    change ‖rows i + parameter‖ /
        (2 * fixedBallCommonRadius Rₓ Rᵧ) ≤
      low / (2 * fixedBallCommonRadius Rₓ Rᵧ)
    exact div_le_div_of_nonneg_right (hlow i hi)
      (mul_nonneg (by norm_num) (fixedBallCommonRadius_pos hRₓ hRᵧ).le)
  · intro i hi
    change high / (2 * fixedBallCommonRadius Rₓ Rᵧ) ≤
      ‖rows i + parameter‖ / (2 * fixedBallCommonRadius Rₓ Rᵧ)
    exact div_le_div_of_nonneg_right (hhigh i hi)
      (mul_nonneg (by norm_num) (fixedBallCommonRadius_pos hRₓ hRᵧ).le)

/-- A zero-radius norm ball is a subsingleton. -/
theorem closedNormBall_zero_subsingleton :
    Subsingleton (ClosedNormBall E 0) := by
  constructor
  intro x y
  apply Subtype.ext
  have hx : x.1 = 0 := norm_eq_zero.mp
    (le_antisymm x.2 (norm_nonneg x.1))
  have hy : y.1 = 0 := norm_eq_zero.mp
    (le_antisymm y.2 (norm_nonneg y.1))
  rw [hx, hy]

/-- A binary formula is NIP whenever its row sort is a subsingleton. -/
theorem MultiFormula.isNIPOnStructure_of_subsingleton_row
    {Symbol : Type*} {M : MultiStructure Symbol}
    [Subsingleton M.Row] (formula : MultiFormula Symbol 1 1) :
    formula.IsNIPOnStructure M := by
  rintro ⟨low, high, hgap, rows, hrows⟩
  obtain ⟨parameter, hlow, hhigh⟩ :=
    hrows {0} {1} (by simp)
  have hle := hlow 0 (by simp)
  have hge := hhigh 1 (by simp)
  rw [Subsingleton.elim (rows 1) (rows 0)] at hge
  linarith

/-- A binary formula is NIP whenever its parameter sort is a subsingleton. -/
theorem MultiFormula.isNIPOnStructure_of_subsingleton_parameter
    {Symbol : Type*} {M : MultiStructure Symbol}
    [Subsingleton M.Parameter] (formula : MultiFormula Symbol 1 1) :
    formula.IsNIPOnStructure M := by
  rintro ⟨low, high, hgap, rows, hrows⟩
  obtain ⟨parameterLow, hlow, _⟩ := hrows {0} ∅ (by simp)
  obtain ⟨parameterHigh, _, hhigh⟩ := hrows ∅ {0} (by simp)
  have hle := hlow 0 (by simp)
  have hge := hhigh 0 (by simp)
  rw [Subsingleton.elim parameterHigh parameterLow] at hge
  linarith

/-- The independent fixed-ball norm formula is automatically NIP when the
row radius is zero. -/
theorem normAddFixedMultiFormula_isNIPOnStructure_zero_row
    (Rᵧ : ℝ) (hRᵧ : 0 ≤ Rᵧ) :
    MultiFormula.IsNIPOnStructure
      (normAddFixedMultiStructure (E := E) 0 Rᵧ le_rfl hRᵧ)
      normAddMultiFormula := by
  letI : Subsingleton
      (normAddFixedMultiStructure (E := E) 0 Rᵧ le_rfl hRᵧ).Row := by
    change Subsingleton (ClosedNormBall E 0)
    exact closedNormBall_zero_subsingleton
  exact MultiFormula.isNIPOnStructure_of_subsingleton_row normAddMultiFormula

/-- The independent fixed-ball norm formula is automatically NIP when the
parameter radius is zero. -/
theorem normAddFixedMultiFormula_isNIPOnStructure_zero_parameter
    (Rₓ : ℝ) (hRₓ : 0 ≤ Rₓ) :
    MultiFormula.IsNIPOnStructure
      (normAddFixedMultiStructure (E := E) Rₓ 0 hRₓ le_rfl)
      normAddMultiFormula := by
  letI : Subsingleton
      (normAddFixedMultiStructure (E := E) Rₓ 0 hRₓ le_rfl).Parameter := by
    change Subsingleton (ClosedNormBall E 0)
    exact closedNormBall_zero_subsingleton
  exact MultiFormula.isNIPOnStructure_of_subsingleton_parameter normAddMultiFormula

end

end NormFormula.ContinuousLogic


namespace NormFormula.X

noncomputable section

open NormFormula.ContinuousLogic

/-- The norm formula is NIP on every independently fixed pair of nonnegative
balls in `X`. -/
theorem normAddFixedMultiFormula_isNIPOnStructure
    (Rₓ Rᵧ : ℝ) (hRₓ : 0 ≤ Rₓ) (hRᵧ : 0 ≤ Rᵧ) :
    MultiFormula.IsNIPOnStructure
      (normAddFixedMultiStructure (E := XSpace) Rₓ Rᵧ hRₓ hRᵧ)
      normAddMultiFormula :=
  normAddFixedMultiFormula_isNIPOnStructure_of_common Rₓ Rᵧ hRₓ hRᵧ
    (normAddMultiFormula_isNIPOnStructure
      (fixedBallCommonRadius Rₓ Rᵧ) (fixedBallCommonRadius_pos hRₓ hRᵧ))

end

end NormFormula.X


namespace NormFormula.HalfGraph.Y

noncomputable section

open NormFormula.ContinuousLogic

/-- The norm formula is NIP on every independently fixed pair of nonnegative
balls in `Y`. -/
theorem normAddFixedMultiFormula_isNIPOnStructure
    (Rₓ Rᵧ : ℝ) (hRₓ : 0 ≤ Rₓ) (hRᵧ : 0 ≤ Rᵧ) :
    MultiFormula.IsNIPOnStructure
      (normAddFixedMultiStructure (E := Y) Rₓ Rᵧ hRₓ hRᵧ)
      normAddMultiFormula :=
  normAddFixedMultiFormula_isNIPOnStructure_of_common Rₓ Rᵧ hRₓ hRᵧ
    (normAddMultiFormula_isNIPOnStructure
      (fixedBallCommonRadius Rₓ Rᵧ) (fixedBallCommonRadius_pos hRₓ hRᵧ))

end

end NormFormula.HalfGraph.Y


namespace NormFormula.XY

noncomputable section

open NormFormula.ContinuousLogic

/-- The norm formula is NIP on every independently fixed pair of nonnegative
balls in `X ⊕₂ Y`. -/
theorem normAddFixedMultiFormula_isNIPOnStructure
    (Rₓ Rᵧ : ℝ) (hRₓ : 0 ≤ Rₓ) (hRᵧ : 0 ≤ Rᵧ) :
    MultiFormula.IsNIPOnStructure
      (normAddFixedMultiStructure (E := XYSpace) Rₓ Rᵧ hRₓ hRᵧ)
      normAddMultiFormula :=
  normAddFixedMultiFormula_isNIPOnStructure_of_common Rₓ Rᵧ hRₓ hRᵧ
    (normAddMultiFormula_isNIPOnStructure
      (fixedBallCommonRadius Rₓ Rᵧ) (fixedBallCommonRadius_pos hRₓ hRᵧ))

end

end NormFormula.XY
