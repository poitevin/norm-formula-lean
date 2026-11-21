import NormFormula.ContinuousLogic.NormAdd
import NormFormula.ContinuousLogic.MultiCompactness
import NormFormula.ContinuousLogic.SeparableElementaryIP

/-!
# Separable elementary norm-predicate models

Raw norm-addition patterns are normalized on a sufficiently large positive
ball, transferred to a same-theory many-predicate reduced product, and then
placed inside the separable elementary witness-limit structure. The exact
normalized thresholds are retained throughout.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Set TopologicalSpace

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.parameterPseudoMetricSpace MultiStructure.rowNonempty
  MultiStructure.parameterNonempty

universe u v

variable {E : Type u} [NormedAddCommGroup E]

/-- Bounds for the many-predicate presentation of a positive norm ball. -/
def normAddMultiStructureBounds (R : ℝ) (hR : 0 < R) :
    (normAddMultiStructure (E := E) R hR).Bounds := by
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

/-- Raw norm patterns give finite patterns for the actual many-predicate
`NormAddSymbol` formula. -/
theorem normAddMulti_hasFinitePatterns_of_raw_patterns
    (R_x R_y low high : ℝ)
    (hpatterns : NormFormula.HasIPPatternsInEveryDimension
      (fun x y : E => ‖x + y‖) R_x R_y low high) :
    let R := 1 + |R_x| + |R_y|
    MultiFormula.HasFiniteIPPatternsInEveryDimension
      (normAddMultiStructure (E := E) R (by positivity))
      normAddMultiFormula (low / (2 * R)) (high / (2 * R)) := by
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
    fun i => ⟨rows i, (hrows i).trans hxR⟩
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

/-- Raw finite patterns yield a same-theory norm-predicate model with one
infinite witness at the exact normalized thresholds. -/
theorem exists_sameTheory_normAddInfiniteWitness_of_patterns
    (R_x R_y low high : ℝ)
    (hpatterns : NormFormula.HasIPPatternsInEveryDimension
      (fun x y : E => ‖x + y‖) R_x R_y low high) :
    let R := 1 + |R_x| + |R_y|
    ∃ N : MultiStructure.{u, u} NormAddSymbol,
      MultiSameCompleteTheory
        (normAddMultiStructure (E := E) R (by positivity)) N ∧
      MultiFormula.HasInfiniteIPWitness N normAddMultiFormula
        (low / (2 * R)) (high / (2 * R)) := by
  dsimp only
  let R := 1 + |R_x| + |R_y|
  have hR : 0 < R := by
    dsimp [R]
    positivity
  exact MultiFormula.exists_sameTheory_atomic_infiniteWitness_of_finitePatterns
    (normAddMultiStructure (E := E) R hR)
    (normAddMultiStructureBounds R hR) .norm
    (low / (2 * R)) (high / (2 * R))
    (by simpa [normAddMultiFormula] using
      (normAddMulti_hasFinitePatterns_of_raw_patterns
        (E := E) R_x R_y low high hpatterns))

/-- Raw norm patterns therefore have a separable same-theory
`NormAddSymbol` model retaining the exact normalized infinite witness. -/
theorem exists_separableNormAddIPModel_of_patterns
    (R_x R_y low high : ℝ)
    (hpatterns : NormFormula.HasIPPatternsInEveryDimension
      (fun x y : E => ‖x + y‖) R_x R_y low high) :
    let R := 1 + |R_x| + |R_y|
    ∃ N : MultiStructure.{u, u} NormAddSymbol,
      MultiSameCompleteTheory
        (normAddMultiStructure (E := E) R (by positivity)) N ∧
      IsSeparable (Set.univ : Set N.Row) ∧
      IsSeparable (Set.univ : Set N.Parameter) ∧
      MultiFormula.HasInfiniteIPWitness N normAddMultiFormula
        (low / (2 * R)) (high / (2 * R)) := by
  dsimp only
  let R := 1 + |R_x| + |R_y|
  obtain ⟨ambient, hAmbientTheory, hAmbientWitness⟩ :=
    exists_sameTheory_normAddInfiniteWitness_of_patterns
      (E := E) R_x R_y low high hpatterns
  obtain ⟨target, hTargetTheory, hRowSeparable, hParameterSeparable,
    hTargetWitness⟩ :=
      MultiFormula.exists_separableElementaryIPSubstructure hAmbientWitness
  exact ⟨target, hAmbientTheory.trans hTargetTheory, hRowSeparable,
    hParameterSeparable, hTargetWitness⟩

end

end NormFormula.ContinuousLogic
