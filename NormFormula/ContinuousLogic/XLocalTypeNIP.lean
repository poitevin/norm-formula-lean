import NormFormula.Analytic.Separability
import NormFormula.ContinuousLogic.NormAddLocalType
import NormFormula.ModelTheory.XStability

/-!
# Local-type NIP for the bounded norm formula on `X`

This file transfers the prepared weak-subsequence calculation for `XSpace`
from realized parameters to the compact local parameter type space.  The key
step compares two successive limits: home parameters approach an arbitrary
local type in one order, while asymptotic Pythagoras computes the other order.
Stability forces the resulting scalar limits to agree.
-/

namespace NormFormula.X

noncomputable section

open Filter TopologicalSpace
open scoped Topology
open NormFormula.ContinuousLogic

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.rowNonempty

/-- The unnormalized Pythagorean candidate attached to a prepared weak limit
inside the radius-`R` ball. -/
def normAddLocalTypePythagoreanCandidate
    (R : ℝ) (hR : 0 < R)
    (weakLimit : PositiveNormBall XSpace R) (differenceLimit : ℝ)
    (type : MultiFormula.LocalParameterType
      (normAddMultiStructure (E := XSpace) R hR) normAddMultiFormula) : ℝ :=
  Real.sqrt
    (((2 * R) * MultiFormula.localTypeValue weakLimit type) ^ 2 +
      differenceLimit ^ 2)

/-- The Pythagorean candidate varies continuously with the local type. -/
theorem continuous_normAddLocalTypePythagoreanCandidate
    (R : ℝ) (hR : 0 < R)
    (weakLimit : PositiveNormBall XSpace R) (differenceLimit : ℝ) :
    Continuous
      (normAddLocalTypePythagoreanCandidate
        R hR weakLimit differenceLimit) := by
  apply Real.continuous_sqrt.comp
  exact
    ((continuous_const.mul
      (MultiFormula.continuous_localTypeValue
        (M := normAddMultiStructure (E := XSpace) R hR)
        (φ := normAddMultiFormula) weakLimit)).pow 2).add
      continuous_const

/-- At a realized home parameter, the candidate is exactly the analytic
Pythagorean limit. -/
theorem normAddLocalTypePythagoreanCandidate_homeParameterType
    (R : ℝ) (hR : 0 < R)
    (weakLimit parameter : PositiveNormBall XSpace R)
    (differenceLimit : ℝ) :
    normAddLocalTypePythagoreanCandidate R hR weakLimit differenceLimit
        (MultiFormula.homeParameterType
          (normAddMultiStructure (E := XSpace) R hR)
          normAddMultiFormula parameter) =
      Real.sqrt (‖parameter.1 + weakLimit.1‖ ^ 2 + differenceLimit ^ 2) := by
  rw [normAddLocalTypePythagoreanCandidate,
    MultiFormula.localTypeValue_homeParameterType,
    normAddMultiFormula_value]
  have hdenom : 2 * R ≠ 0 := ne_of_gt (by positivity)
  rw [mul_div_cancel₀ _ hdenom, add_comm parameter.1 weakLimit.1]

/-- Stability identifies every convergent subsequential value at an arbitrary
local type with the continuous Pythagorean candidate.  This is the central
double-limit comparison in the `X` local-type proof. -/
theorem localType_subsequentialLimit_eq_pythagoreanCandidate
    (R : ℝ) (hR : 0 < R)
    (rows : ℕ → PositiveNormBall XSpace R)
    (weakLimit : PositiveNormBall XSpace R) (differenceLimit scalarLimit : ℝ)
    [FrechetUrysohnSpace (MultiFormula.LocalParameterType
      (normAddMultiStructure (E := XSpace) R hR) normAddMultiFormula)]
    (hrowsWeak : WeaklyTendsto (fun n ↦ (rows n).1) atTop weakLimit.1)
    (hrowsDifference : Tendsto
      (fun n ↦ ‖(rows n).1 - weakLimit.1‖) atTop (nhds differenceLimit))
    (hrowsDifferenceBound : ∀ n,
      ‖(rows n).1 - weakLimit.1‖ ≤ R + ‖weakLimit.1‖)
    (type : MultiFormula.LocalParameterType
      (normAddMultiStructure (E := XSpace) R hR) normAddMultiFormula)
    (hscalar : Tendsto
      (fun n ↦ MultiFormula.localTypeValue (rows n) type)
      atTop (nhds scalarLimit)) :
    scalarLimit =
      normAddLocalTypePythagoreanCandidate
        R hR weakLimit differenceLimit type / (2 * R) := by
  obtain ⟨parameters, hparameters⟩ :=
    MultiFormula.exists_homeParameter_sequence_tendsto
      (normAddMultiStructure (E := XSpace) R hR)
      normAddMultiFormula type
  have hdenom : 2 * R ≠ 0 := ne_of_gt (by positivity)
  have hfirst : HasSuccessiveLimit
      (fun m n ↦ normTranslate (rows m).1 (parameters n).1)
      ((2 * R) * scalarLimit) := by
    refine ⟨fun m ↦ (2 * R) * MultiFormula.localTypeValue (rows m) type,
      ?_, ?_⟩
    · intro m
      have hcoordinateTruth :=
        (MultiFormula.tendsto_localParameterType_iff_pointwise.mp hparameters)
          (rows m)
      have hcoordinate : Tendsto
          (fun n ↦ MultiFormula.localTypeValue (rows m)
            (MultiFormula.homeParameterType
              (normAddMultiStructure (E := XSpace) R hR)
              normAddMultiFormula (parameters n)))
          atTop
          (nhds (MultiFormula.localTypeValue (rows m) type)) :=
        continuous_subtype_val.continuousAt.tendsto.comp hcoordinateTruth
      have hconstant : Tendsto (fun _ : ℕ ↦ 2 * R) atTop (nhds (2 * R)) :=
        tendsto_const_nhds
      have hscaled := hconstant.mul hcoordinate
      convert hscaled using 1
      funext n
      change ‖(rows m).1 + (parameters n).1‖ =
        (2 * R) * (‖(rows m).1 + (parameters n).1‖ / (2 * R))
      field_simp
    · exact tendsto_const_nhds.mul hscalar
  have hsecond : HasSuccessiveLimit
      (fun n m ↦ normTranslate (rows m).1 (parameters n).1)
      (normAddLocalTypePythagoreanCandidate
        R hR weakLimit differenceLimit type) := by
    refine ⟨fun n ↦ normAddLocalTypePythagoreanCandidate
        R hR weakLimit differenceLimit
        (MultiFormula.homeParameterType
          (normAddMultiStructure (E := XSpace) R hR)
          normAddMultiFormula (parameters n)), ?_, ?_⟩
    · intro n
      have hparameter := tendsto_norm_add_of_weaklyTendsto
        (parameters n).1 hrowsWeak hrowsDifferenceBound hrowsDifference
      convert hparameter using 1
      · funext m
        exact add_comm (rows m).1 (parameters n).1 ▸ rfl
      · exact congrArg nhds
          (normAddLocalTypePythagoreanCandidate_homeParameterType
            R hR weakLimit (parameters n) differenceLimit)
    · exact
        (continuous_normAddLocalTypePythagoreanCandidate
          R hR weakLimit differenceLimit).continuousAt.tendsto.comp hparameters
  have heq : (2 * R) * scalarLimit =
      normAddLocalTypePythagoreanCandidate
        R hR weakLimit differenceLimit type := by
    exact normTranslate_isStableOnBounded
      (fun n ↦ (rows n).1) (fun n ↦ (parameters n).1)
      R R ((2 * R) * scalarLimit)
      (normAddLocalTypePythagoreanCandidate
        R hR weakLimit differenceLimit type)
      (fun n ↦ (rows n).2) (fun n ↦ (parameters n).2)
      hfirst hsecond
  rw [eq_div_iff hdenom]
  simpa only [mul_comm] using heq

/-- On every positive `XSpace`-ball, every row sequence has a subsequence
whose normalized norm evaluations converge pointwise on the full concrete
local parameter type space. -/
theorem normAddMultiFormula_hasPointwiseConvergentSubsequenceOnLocalType
    (R : ℝ) (hR : 0 < R) :
    MultiFormula.HasPointwiseConvergentSubsequenceOnLocalType
      (normAddMultiStructure (E := XSpace) R hR) normAddMultiFormula := by
  letI : SeparableSpace
      (normAddMultiStructure (E := XSpace) R hR).Row :=
    inferInstanceAs (SeparableSpace (PositiveNormBall XSpace R))
  letI : MetrizableSpace (MultiFormula.LocalParameterType
      (normAddMultiStructure (E := XSpace) R hR) normAddMultiFormula) :=
    MultiFormula.localParameterTypeMetrizableSpace
      (normAddMultiStructure (E := XSpace) R hR) normAddMultiFormula
      ⟨1 / (2 * R), by positivity⟩
      (MultiFormula.normAddMultiFormula_parameterProfilesLipschitzWith R hR)
  intro rows
  obtain ⟨weakLimit, subsequence, differenceLimit, hsubsequence,
      hrowsWeak, hrowsDifference, hrowsDifferenceBound⟩ :=
    weakSequentialCompactnessOnBounded.exists_prepared_subsequence_in_ball
      (fun n ↦ (rows n).1) R (fun n ↦ (rows n).2)
  refine ⟨subsequence, hsubsequence, ?_⟩
  intro type
  let candidate : ℝ :=
    normAddLocalTypePythagoreanCandidate
      R hR weakLimit differenceLimit type / (2 * R)
  refine ⟨candidate, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra hnot
  push Not at hnot
  have hfrequent : ∃ᶠ n in atTop,
      ε ≤ dist
        (MultiFormula.localTypeValue (rows (subsequence n)) type)
        candidate := by
    rw [frequently_atTop]
    exact hnot
  obtain ⟨badSubsequence, hbadSubsequence, hbad⟩ :=
    extraction_of_frequently_atTop hfrequent
  let scalarProfiles : ℕ → TruthValue := fun n ↦
    MultiFormula.localTypeTruthValue
      (rows (subsequence (badSubsequence n))) type
  obtain ⟨scalarLimit, furtherSubsequence, hfurtherSubsequence,
      hscalarTruth⟩ := SeqCompactSpace.tendsto_subseq scalarProfiles
  let selectedRows : ℕ → PositiveNormBall XSpace R := fun n ↦
    rows (subsequence (badSubsequence (furtherSubsequence n)))
  have hselection : StrictMono
      (badSubsequence ∘ furtherSubsequence) :=
    hbadSubsequence.comp hfurtherSubsequence
  have hselectedWeak : WeaklyTendsto
      (fun n ↦ (selectedRows n).1) atTop weakLimit.1 := by
    simpa [selectedRows, Function.comp_def, Function.comp_assoc] using
      hrowsWeak.comp_tendsto hselection.tendsto_atTop
  have hselectedDifference : Tendsto
      (fun n ↦ ‖(selectedRows n).1 - weakLimit.1‖)
      atTop (nhds differenceLimit) := by
    simpa [selectedRows, Function.comp_def] using
      hrowsDifference.comp hselection.tendsto_atTop
  have hselectedDifferenceBound : ∀ n,
      ‖(selectedRows n).1 - weakLimit.1‖ ≤ R + ‖weakLimit.1‖ := by
    intro n
    exact hrowsDifferenceBound
      (badSubsequence (furtherSubsequence n))
  have hscalar : Tendsto
      (fun n ↦ MultiFormula.localTypeValue (selectedRows n) type)
      atTop (nhds (scalarLimit : ℝ)) := by
    simpa [selectedRows, scalarProfiles, Function.comp_def] using
      continuous_subtype_val.continuousAt.tendsto.comp hscalarTruth
  have hlimitEq : (scalarLimit : ℝ) = candidate := by
    exact localType_subsequentialLimit_eq_pythagoreanCandidate
      R hR selectedRows weakLimit differenceLimit scalarLimit
      hselectedWeak hselectedDifference hselectedDifferenceBound type hscalar
  have hdistLimit : Tendsto
      (fun n ↦ dist
        (MultiFormula.localTypeValue (selectedRows n) type) candidate)
      atTop (nhds (dist (scalarLimit : ℝ) candidate)) :=
    hscalar.dist tendsto_const_nhds
  have hseparated : ε ≤ dist (scalarLimit : ℝ) candidate :=
    ge_of_tendsto hdistLimit <| Eventually.of_forall fun n ↦
      hbad (furtherSubsequence n)
  rw [hlimitEq, dist_self] at hseparated
  exact (not_le_of_gt hε) hseparated

/-- Hence the normalized norm formula is NIP on every distinguished positive
ball of `XSpace`. -/
theorem normAddMultiFormula_isNIPOnStructure
    (R : ℝ) (hR : 0 < R) :
    MultiFormula.IsNIPOnStructure
      (normAddMultiStructure (E := XSpace) R hR) normAddMultiFormula :=
  MultiFormula.isNIPOnStructure_of_pointwiseConvergentSubsequenceOnLocalType
    (normAddMultiFormula_hasPointwiseConvergentSubsequenceOnLocalType R hR)

end

end NormFormula.X
