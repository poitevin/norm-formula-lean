import NormFormula.ContinuousLogic.L2SumLocalNIP
import NormFormula.ContinuousLogic.XLocalTypeNIP
import NormFormula.ContinuousLogic.XYLocalType
import NormFormula.ContinuousLogic.YLocalTypeNIP

/-!
# Local-type NIP for the bounded direct sum

The two factor pointwise-subsequence theorems are diagonalized.  Surjectivity
of the joint-factor Euclidean map identifies every direct-sum local type with
a jointly realizable pair of factor types, so coordinatewise convergence and
continuity of the Euclidean connective give convergence on the full sum type
space.
-/

namespace NormFormula.XY

noncomputable section

open Filter
open scoped Topology
open NormFormula.ContinuousLogic

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.rowNonempty

@[simp]
theorem localTypeValue_jointNormFactorTypeMap
    (R : ℝ) (hR : 0 < R)
    (row : PositiveNormBall XYSpace R)
    (type : JointNormFactorType R hR) :
    MultiFormula.localTypeValue row
        (jointNormFactorTypeMap R hR type) =
      jointNormFactorValue R hR row type :=
  rfl

/-- On every positive direct-sum ball, every row sequence has a subsequence
whose normalized norm evaluations converge pointwise on the entire concrete
local parameter type space. -/
theorem normAddMultiFormula_hasPointwiseConvergentSubsequenceOnLocalType
    (R : ℝ) (hR : 0 < R) :
    MultiFormula.HasPointwiseConvergentSubsequenceOnLocalType
      (normAddMultiStructure (E := XYSpace) R hR) normAddMultiFormula := by
  intro rows
  obtain ⟨xSubsequence, hxSubsequence, hxConverges⟩ :=
    NormFormula.X.normAddMultiFormula_hasPointwiseConvergentSubsequenceOnLocalType
      R hR (fun n ↦ positiveNormBallFst R (rows n))
  obtain ⟨ySubsequence, hySubsequence, hyConverges⟩ :=
    NormFormula.HalfGraph.Y.normAddMultiFormula_hasPointwiseConvergentSubsequenceOnLocalType
      R hR (fun n ↦ positiveNormBallSnd R (rows (xSubsequence n)))
  refine ⟨xSubsequence ∘ ySubsequence,
    hxSubsequence.comp hySubsequence, ?_⟩
  intro sumType
  obtain ⟨jointType, hjointType⟩ :=
    jointNormFactorTypeMap_surjective R hR sumType
  obtain ⟨xLimit, hxLimit⟩ := hxConverges jointType.1.1
  have hxLimit' : Tendsto
      (fun n ↦ MultiFormula.localTypeValue
        (positiveNormBallFst R
          (rows ((xSubsequence ∘ ySubsequence) n))) jointType.1.1)
      atTop (𝓝 xLimit) := by
    simpa [Function.comp_def] using hxLimit.comp hySubsequence.tendsto_atTop
  obtain ⟨yLimit, hyLimit⟩ := hyConverges jointType.1.2
  refine ⟨NormFormula.euclideanConnective xLimit yLimit, ?_⟩
  have hpair : Tendsto
      (fun n ↦
        (MultiFormula.localTypeValue
          (positiveNormBallFst R
            (rows ((xSubsequence ∘ ySubsequence) n))) jointType.1.1,
          MultiFormula.localTypeValue
            (positiveNormBallSnd R
              (rows ((xSubsequence ∘ ySubsequence) n))) jointType.1.2))
      atTop (𝓝 (xLimit, yLimit)) := by
    exact hxLimit'.prodMk_nhds (by
      simpa [Function.comp_def] using hyLimit)
  have hcombined :=
    NormFormula.euclideanConnective_uniformContinuous.continuous.continuousAt.tendsto.comp
      hpair
  rw [← hjointType]
  simpa [MultiFormula.localTypeEvaluationSequence,
    jointNormFactorValue, Function.comp_def] using hcombined

/-- Hence the normalized norm formula is NIP on every distinguished positive
ball of `X ⊕₂ Y`. -/
theorem normAddMultiFormula_isNIPOnStructure
    (R : ℝ) (hR : 0 < R) :
    MultiFormula.IsNIPOnStructure
      (normAddMultiStructure (E := XYSpace) R hR) normAddMultiFormula :=
  normAddMultiFormula_isNIPOnStructure_l2Sum R hR
    (X.normAddMultiFormula_isNIPOnStructure R hR)
    (HalfGraph.Y.normAddMultiFormula_isNIPOnStructure R hR)

end

end NormFormula.XY
