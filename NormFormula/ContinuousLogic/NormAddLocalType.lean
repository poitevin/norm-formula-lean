import NormFormula.ContinuousLogic.LocalTypeNIP
import NormFormula.ContinuousLogic.NormAdd
import NormFormula.ModelTheory.LocalNIP

/-!
# Local type data for generic norm-addition balls

The normalized norm predicate on an arbitrary positive ball is presented in
the one-symbol many-predicate language from `NormAdd`.  Its realized parameter
profiles share the sharp Lipschitz constant `1 / (2R)`.  This is the common
local-type input for the concrete `X`, `Y`, and direct-sum structures.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u

namespace MultiFormula

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.rowNonempty

variable {E : Type u} [NormedAddCommGroup E]

/-- Every realized parameter profile of normalized norm addition on the
positive `R`-ball is `1 / (2R)`-Lipschitz in its row variable. -/
theorem normAddMultiFormula_parameterProfilesLipschitzWith
    (R : ℝ) (hR : 0 < R) :
    ParameterProfilesLipschitzWith
      (normAddMultiStructure (E := E) R hR) normAddMultiFormula
      ⟨1 / (2 * R), by positivity⟩ := by
  intro parameter
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [parameterProfile_apply]
  change dist (normAddTruth R hR x parameter)
      (normAddTruth R hR y parameter) ≤
    (1 / (2 * R)) * dist x y
  rw [Subtype.dist_eq, Real.dist_eq]
  change |‖x.1 + parameter.1‖ / (2 * R) -
      ‖y.1 + parameter.1‖ / (2 * R)| ≤
    (1 / (2 * R)) * dist x y
  rw [← sub_div, abs_div, abs_of_pos (by positivity : 0 < 2 * R)]
  calc
    |‖x.1 + parameter.1‖ - ‖y.1 + parameter.1‖| / (2 * R) ≤
        ‖(x.1 + parameter.1) - (y.1 + parameter.1)‖ / (2 * R) :=
      div_le_div_of_nonneg_right
        (abs_norm_sub_norm_le _ _) (by positivity)
    _ = (1 / (2 * R)) * dist x y := by
      rw [add_sub_add_right_eq_sub,
        show dist x y = ‖x.1 - y.1‖ by
          change dist (x.1 : E) y.1 = ‖x.1 - y.1‖
          rw [dist_eq_norm]]
      field_simp

/-- Bounded local NIP of the unnormalized norm translation rules out an
infinite IP witness for its normalized formula on every positive ball.  This
is the common bridge from the paper's quantitative whole-space notion to NIP
on the distinguished bounded continuous structure. -/
theorem normAddMultiFormula_isNIPOnStructure_of_boundedLocalNIP
    (R : ℝ) (hR : 0 < R)
    (hlocal : NormFormula.IsBoundedLocalNIP
      (fun x y : E ↦ ‖x + y‖)) :
    IsNIPOnStructure
      (normAddMultiStructure (E := E) R hR) normAddMultiFormula := by
  classical
  rintro ⟨low, high, hgap, rows, hrows⟩
  have hdenom : 0 < 2 * R := by positivity
  obtain ⟨N, hN⟩ := hlocal R R
    (low * (2 * R)) (high * (2 * R))
    (mul_lt_mul_of_pos_right hgap hdenom)
  apply (Nat.lt_irrefl N)
  apply hN N (fun i ↦ (rows i).1) (fun i ↦ (rows i).2)
  intro S
  let embedding : Fin N ↪ ℕ := Fin.valEmbedding
  let lowSet : Finset ℕ := (Finset.univ \ S).map embedding
  let highSet : Finset ℕ := S.map embedding
  have hdisjoint : Disjoint lowSet highSet := by
    exact (Finset.disjoint_map embedding).2 Finset.sdiff_disjoint
  obtain ⟨parameter, hlow, hhigh⟩ :=
    hrows lowSet highSet hdisjoint
  refine ⟨parameter, ?_, ?_⟩
  · intro i hi
    have hi' := hhigh i
      (Finset.mem_map.mpr ⟨i, hi, rfl⟩)
    change high ≤ ‖(rows i).1 + parameter.1‖ / (2 * R) at hi'
    exact (le_div_iff₀ hdenom).mp hi'
  · intro i hi
    have hi' := hlow i
      (Finset.mem_map.mpr
        ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩)
    change ‖(rows i).1 + parameter.1‖ / (2 * R) ≤ low at hi'
    exact (div_le_iff₀ hdenom).mp hi'

end MultiFormula

/-- Local NIP of the norm formula on an unbounded normed structure, expressed
in the bounded-sorts presentation used by continuous logic: the generic
normalized formula is NIP on every positive radius ball. -/
def NormFormulaIsNIPOnPositiveBalls
    (E : Type u) [NormedAddCommGroup E] : Prop :=
  ∀ (R : ℝ) (hR : 0 < R),
    MultiFormula.IsNIPOnStructure
      (normAddMultiStructure (E := E) R hR) normAddMultiFormula

end

end NormFormula.ContinuousLogic
