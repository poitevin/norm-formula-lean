import NormFormula.ContinuousLogic.NormAddLocalType
import NormFormula.ModelTheory.ConnectiveClosure
import Mathlib.Analysis.Normed.Lp.ProdLp

/-! # Distinguished-space NIP under finite ℓ₂ sums

The compact product of the two factor type spaces is sufficient to test an
independent sequence. Successive subsequences give convergence on both
factors, and the Euclidean connective gives convergence on their product.
-/

namespace NormFormula.ContinuousLogic
noncomputable section
open Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem normAddMultiFormula_isNIPOnStructure_l2Sum
    (R : ℝ) (hR : 0 < R)
    (hE : MultiFormula.IsNIPOnStructure
      (normAddMultiStructure (E := E) R hR) normAddMultiFormula)
    (hF : MultiFormula.IsNIPOnStructure
      (normAddMultiStructure (E := F) R hR) normAddMultiFormula) :
    MultiFormula.IsNIPOnStructure
      (normAddMultiStructure (E := WithLp 2 (E × F)) R hR) normAddMultiFormula := by
  rintro ⟨low, high, hgap, rows, hrows⟩
  let fstBall (z : PositiveNormBall (WithLp 2 (E × F)) R) : PositiveNormBall E R :=
    ⟨z.1.fst, (WithLp.norm_fst_le E z.1).trans z.2⟩
  let sndBall (z : PositiveNormBall (WithLp 2 (E × F)) R) : PositiveNormBall F R :=
    ⟨z.1.snd, (WithLp.norm_snd_le E z.1).trans z.2⟩
  let PE := MultiFormula.LocalParameterType (normAddMultiStructure (E := E) R hR)
    normAddMultiFormula
  let PF := MultiFormula.LocalParameterType (normAddMultiStructure (E := F) R hR)
    normAddMultiFormula
  let value : ℕ → PE × PF → ℝ := fun n p ↦
    euclideanConnective (MultiFormula.localTypeValue (fstBall (rows n)) p.1)
      (MultiFormula.localTypeValue (sndBall (rows n)) p.2)
  have heq (x y : PositiveNormBall (WithLp 2 (E × F)) R) :
      euclideanConnective
        (normAddMultiFormula.binaryValue (normAddMultiStructure (E := E) R hR)
          (fstBall x) (fstBall y))
        (normAddMultiFormula.binaryValue (normAddMultiStructure (E := F) R hR)
          (sndBall x) (sndBall y)) =
      normAddMultiFormula.binaryValue
        (normAddMultiStructure (E := WithLp 2 (E × F)) R hR) x y := by
    change Real.sqrt ((‖x.1.fst + y.1.fst‖ / (2 * R)) ^ 2 +
      (‖x.1.snd + y.1.snd‖ / (2 * R)) ^ 2) = ‖x.1 + y.1‖ / (2 * R)
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), div_pow, div_pow, div_pow,
      WithLp.prod_norm_sq_eq_of_L2]
    simp only [WithLp.add_fst, WithLp.add_snd, add_div]
  have hind : MultiFormula.HasIndependentSequence value := by
    refine ⟨low, high, hgap, ?_⟩
    intro A B hAB
    obtain ⟨y, hyA, hyB⟩ := hrows A B hAB
    refine ⟨(MultiFormula.homeParameterType _ _ (fstBall y),
      MultiFormula.homeParameterType _ _ (sndBall y)), ?_, ?_⟩
    · intro i hi
      change euclideanConnective _ _ ≤ low
      rw [MultiFormula.localTypeValue_homeParameterType,
        MultiFormula.localTypeValue_homeParameterType, heq]
      exact hyA i hi
    · intro i hi
      change high ≤ euclideanConnective _ _
      rw [MultiFormula.localTypeValue_homeParameterType,
        MultiFormula.localTypeValue_homeParameterType, heq]
      exact hyB i hi
  have hcont : ∀ n, Continuous (value n) := by
    intro n
    exact euclideanConnective_uniformContinuous.continuous.comp
      (((MultiFormula.continuous_localTypeValue (M := normAddMultiStructure (E := E) R hR) (φ := normAddMultiFormula) (fstBall (rows n))).comp continuous_fst).prodMk
        ((MultiFormula.continuous_localTypeValue (M := normAddMultiStructure (E := F) R hR) (φ := normAddMultiFormula) (sndBall (rows n))).comp continuous_snd))
  obtain ⟨φ, hφ, hφconv⟩ :=
    MultiFormula.isNIPOnStructure_iff_pointwiseConvergentSubsequenceOnLocalType_general.mp
      hE (fun n ↦ fstBall (rows n))
  obtain ⟨ψ, hψ, hψconv⟩ :=
    MultiFormula.isNIPOnStructure_iff_pointwiseConvergentSubsequenceOnLocalType_general.mp
      hF (fun n ↦ sndBall (rows (φ n)))
  apply hind.no_pointwiseConvergence_along hcont (φ ∘ ψ) (hφ.comp hψ)
  intro p
  obtain ⟨a, ha⟩ := hφconv p.1
  obtain ⟨b, hb⟩ := hψconv p.2
  exact ⟨euclideanConnective a b,
    euclideanConnective_uniformContinuous.continuous.continuousAt.tendsto.comp
      ((ha.comp hψ.tendsto_atTop).prodMk_nhds hb)⟩

/-- In particular, the paper's lemma for arbitrary separable Banach spaces.
The proof actually requires neither separability nor completeness. -/
theorem normFormulaIsNIPOnPositiveBalls_l2Sum
    (hE : NormFormulaIsNIPOnPositiveBalls E)
    (hF : NormFormulaIsNIPOnPositiveBalls F) :
    NormFormulaIsNIPOnPositiveBalls (WithLp 2 (E × F)) :=
  fun R hR ↦ normAddMultiFormula_isNIPOnStructure_l2Sum R hR (hE R hR) (hF R hR)

end
end NormFormula.ContinuousLogic
