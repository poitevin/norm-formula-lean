import NormFormula.Analytic.HilbertStability
import NormFormula.ContinuousLogic.NormAddLocalType
import NormFormula.ModelTheory.SeparableIPModel

/-! # Hilbert local NIP from stability

Prepared weak subsequences give Pythagorean limits. The double-limit
stability theorem identifies these limits on every local parameter type.
-/
namespace NormFormula.Hilbert

noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

open Filter TopologicalSpace
open scoped Topology
open NormFormula.ContinuousLogic

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.rowNonempty

/-- The unnormalized Pythagorean candidate attached to a prepared weak limit
inside the radius-`R` ball. -/
def normAddLocalTypePythagoreanCandidate
    (R : ℝ) (hR : 0 < R)
    (weakLimit : PositiveNormBall H R) (differenceLimit : ℝ)
    (type : MultiFormula.LocalParameterType
      (normAddMultiStructure (E := H) R hR) normAddMultiFormula) : ℝ :=
  Real.sqrt
    (((2 * R) * MultiFormula.localTypeValue weakLimit type) ^ 2 +
      differenceLimit ^ 2)

omit [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H] in
/-- The Pythagorean candidate varies continuously with the local type. -/
theorem continuous_normAddLocalTypePythagoreanCandidate
    (R : ℝ) (hR : 0 < R)
    (weakLimit : PositiveNormBall H R) (differenceLimit : ℝ) :
    Continuous
      (normAddLocalTypePythagoreanCandidate
        R hR weakLimit differenceLimit) := by
  apply Real.continuous_sqrt.comp
  exact
    ((continuous_const.mul
      (MultiFormula.continuous_localTypeValue
        (M := normAddMultiStructure (E := H) R hR)
        (φ := normAddMultiFormula) weakLimit)).pow 2).add
      continuous_const

omit [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H] in
/-- At a realized home parameter, the candidate is exactly the analytic
Pythagorean limit. -/
theorem normAddLocalTypePythagoreanCandidate_homeParameterType
    (R : ℝ) (hR : 0 < R)
    (weakLimit parameter : PositiveNormBall H R)
    (differenceLimit : ℝ) :
    normAddLocalTypePythagoreanCandidate R hR weakLimit differenceLimit
        (MultiFormula.homeParameterType
          (normAddMultiStructure (E := H) R hR)
          normAddMultiFormula parameter) =
      Real.sqrt (‖parameter.1 + weakLimit.1‖ ^ 2 + differenceLimit ^ 2) := by
  rw [normAddLocalTypePythagoreanCandidate,
    MultiFormula.localTypeValue_homeParameterType,
    normAddMultiFormula_value]
  have hdenom : 2 * R ≠ 0 := ne_of_gt (by positivity)
  rw [mul_div_cancel₀ _ hdenom, add_comm parameter.1 weakLimit.1]

/-- Stability identifies every convergent subsequential value at an arbitrary
local type with the continuous Pythagorean candidate.  This is the central
double-limit comparison in the Hilbert local-type proof. -/
theorem localType_subsequentialLimit_eq_pythagoreanCandidate
    (R : ℝ) (hR : 0 < R)
    (rows : ℕ → PositiveNormBall H R)
    (weakLimit : PositiveNormBall H R) (differenceLimit scalarLimit : ℝ)
    [FrechetUrysohnSpace (MultiFormula.LocalParameterType
      (normAddMultiStructure (E := H) R hR) normAddMultiFormula)]
    (hrowsWeak : WeaklyTendsto (fun n ↦ (rows n).1) atTop weakLimit.1)
    (hrowsDifference : Tendsto
      (fun n ↦ ‖(rows n).1 - weakLimit.1‖) atTop (nhds differenceLimit))
    (type : MultiFormula.LocalParameterType
      (normAddMultiStructure (E := H) R hR) normAddMultiFormula)
    (hscalar : Tendsto
      (fun n ↦ MultiFormula.localTypeValue (rows n) type)
      atTop (nhds scalarLimit)) :
    scalarLimit =
      normAddLocalTypePythagoreanCandidate
        R hR weakLimit differenceLimit type / (2 * R) := by
  obtain ⟨parameters, hparameters⟩ :=
    MultiFormula.exists_homeParameter_sequence_tendsto
      (normAddMultiStructure (E := H) R hR)
      normAddMultiFormula type
  have hdenom : 2 * R ≠ 0 := ne_of_gt (by positivity)
  have hfirst : HasSuccessiveLimit
      (fun m n ↦ ‖(rows m).1 + (parameters n).1‖)
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
              (normAddMultiStructure (E := H) R hR)
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
      (fun n m ↦ ‖(rows m).1 + (parameters n).1‖)
      (normAddLocalTypePythagoreanCandidate
        R hR weakLimit differenceLimit type) := by
    refine ⟨fun n ↦ normAddLocalTypePythagoreanCandidate
        R hR weakLimit differenceLimit
        (MultiFormula.homeParameterType
          (normAddMultiStructure (E := H) R hR)
          normAddMultiFormula (parameters n)), ?_, ?_⟩
    · intro n
      have hparameter : Tendsto (fun m ↦ ‖(parameters n).1 + (rows m).1‖)
          atTop (𝓝 (Real.sqrt (‖(parameters n).1 + weakLimit.1‖ ^ 2 + differenceLimit ^ 2))) := by
        simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using
          Real.continuous_sqrt.continuousAt.tendsto.comp
            (hilbert_tendsto_norm_add_sq (parameters n).1 hrowsWeak hrowsDifference)
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
    exact hilbert_norm_isStableOnBounded_separable
      (fun n ↦ (rows n).1) (fun n ↦ (parameters n).1)
      R R ((2 * R) * scalarLimit)
      (normAddLocalTypePythagoreanCandidate
        R hR weakLimit differenceLimit type)
      (fun n ↦ (rows n).2) (fun n ↦ (parameters n).2)
      hfirst hsecond
  rw [eq_div_iff hdenom]
  simpa only [mul_comm] using heq

/-- On every positive Hilbert ball, every row sequence has a subsequence
whose normalized norm evaluations converge pointwise on the full concrete
local parameter type space. -/
theorem normAddMultiFormula_hasPointwiseConvergentSubsequenceOnLocalType
    (R : ℝ) (hR : 0 < R) :
    MultiFormula.HasPointwiseConvergentSubsequenceOnLocalType
      (normAddMultiStructure (E := H) R hR) normAddMultiFormula := by
  letI : SeparableSpace
      (normAddMultiStructure (E := H) R hR).Row :=
    inferInstanceAs (SeparableSpace (PositiveNormBall H R))
  letI : MetrizableSpace (MultiFormula.LocalParameterType
      (normAddMultiStructure (E := H) R hR) normAddMultiFormula) :=
    MultiFormula.localParameterTypeMetrizableSpace
      (normAddMultiStructure (E := H) R hR) normAddMultiFormula
      ⟨1 / (2 * R), by positivity⟩
      (MultiFormula.normAddMultiFormula_parameterProfilesLipschitzWith R hR)
  intro rows
  obtain ⟨weakLimit, subsequence, differenceLimit, hsubsequence,
      hrowsWeak, hrowsDifference, _hrowsDifferenceBound⟩ :=
    hilbert_weakSequentialCompactnessOnBounded.exists_prepared_subsequence_in_ball
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
  let selectedRows : ℕ → PositiveNormBall H R := fun n ↦
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
  have hscalar : Tendsto
      (fun n ↦ MultiFormula.localTypeValue (selectedRows n) type)
      atTop (nhds (scalarLimit : ℝ)) := by
    simpa [selectedRows, scalarProfiles, Function.comp_def] using
      continuous_subtype_val.continuousAt.tendsto.comp hscalarTruth
  have hlimitEq : (scalarLimit : ℝ) = candidate := by
    exact localType_subsequentialLimit_eq_pythagoreanCandidate
      R hR selectedRows weakLimit differenceLimit scalarLimit
      hselectedWeak hselectedDifference type hscalar
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
ball of `H`. -/
theorem normAddMultiFormula_isNIPOnStructure
    (R : ℝ) (hR : 0 < R) :
    MultiFormula.IsNIPOnStructure
      (normAddMultiStructure (E := H) R hR) normAddMultiFormula :=
  MultiFormula.isNIPOnStructure_of_pointwiseConvergentSubsequenceOnLocalType
    (normAddMultiFormula_hasPointwiseConvergentSubsequenceOnLocalType R hR)

/-- Stability rules out a bounded infinite norm IP witness in a separable
Hilbert space. -/
theorem not_hasBoundedInfiniteIPWitness_separable
    {R S low high : ℝ} (hgap : low < high) :
    ¬ HasBoundedInfiniteIPWitness (fun x y : H ↦ ‖x + y‖) R S low high := by
  rintro ⟨rows, hrows, hip⟩
  let B := 1 + |R| + |S|
  have hB : 0 < B := by dsimp [B]; positivity
  have hR : R ≤ B := by dsimp [B]; linarith [le_abs_self R, abs_nonneg S]
  have hS : S ≤ B := by dsimp [B]; linarith [le_abs_self S, abs_nonneg R]
  apply normAddMultiFormula_isNIPOnStructure (H := H) B hB
  refine ⟨low / (2 * B), high / (2 * B),
    (div_lt_div_iff_of_pos_right (by positivity)).mpr hgap,
    fun i ↦ ⟨rows i, (hrows i).trans hR⟩, ?_⟩
  intro A C hAC
  obtain ⟨y, hy, hlo, hhi⟩ := hip A C hAC
  refine ⟨⟨y, hy.trans hS⟩, ?_, ?_⟩
  · intro i hi
    exact div_le_div_of_nonneg_right (hlo i hi) (by positivity)
  · intro i hi
    exact div_le_div_of_nonneg_right (hhi i hi) (by positivity)

omit [TopologicalSpace.SeparableSpace H] in
/-- Any putative witness lies in the separable closed span of its countably
many rows and finite-pattern parameters. This removes separability. -/
theorem not_hasBoundedInfiniteIPWitness
    {R S low high : ℝ} (hgap : low < high) :
    ¬ HasBoundedInfiniteIPWitness (fun x y : H ↦ ‖x + y‖) R S low high := by
  classical
  rintro ⟨rows, hrows, hip⟩
  let I := {q : Finset ℕ × Finset ℕ // Disjoint q.1 q.2}
  choose p hp hlo hhi using fun q : I ↦ hip q.1.1 q.1.2 q.2
  let K := (Submodule.span ℝ (Set.range rows ∪ Set.range p)).topologicalClosure
  have hsep : IsSeparable (K : Set H) :=
    ((Set.countable_range rows).union (Set.countable_range p)).isSeparable.span.closure
  letI : NormedAddCommGroup K := inferInstance
  letI : InnerProductSpace ℝ K := inferInstance
  letI : SeparableSpace K := hsep.separableSpace
  letI : CompleteSpace K := (show IsClosed (K : Set H) from
    Submodule.isClosed_topologicalClosure _).completeSpace_coe
  apply @not_hasBoundedInfiniteIPWitness_separable K _ _ ‹CompleteSpace K›
    ‹SeparableSpace K› R S low high hgap
  let r' (i : ℕ) : K := ⟨rows i, Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_union_left _ (Set.mem_range_self i)))⟩
  let p' (q : I) : K := ⟨p q, Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_union_right _ (Set.mem_range_self q)))⟩
  refine ⟨r', hrows, ?_⟩
  intro A C hAC
  exact ⟨p' ⟨(A,C), hAC⟩, hp ⟨(A,C), hAC⟩, hlo ⟨(A,C), hAC⟩, hhi ⟨(A,C), hAC⟩⟩

end

end NormFormula.Hilbert
