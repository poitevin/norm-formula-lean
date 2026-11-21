import NormFormula.Analytic.Separability
import NormFormula.Analytic.XYUniformConvex
import NormFormula.ContinuousLogic.XYLocalTypeNIP
import NormFormula.ContinuousLogic.XYTheoryIP
import NormFormula.Examples.XYInstability
import NormFormula.ModelTheory.XYLocalNIP
import NormFormula.ModelTheory.XYTheoryIP

/-!
# The direct-sum corollary

This file assembles the local logical behavior and complete-theory behavior
of the norm formula on `X ⊕₂ Y`. It also packages the unconditional
separability, midpoint estimate, and quantitative Hilbert equivalence proved
for the concrete direct sum.
-/

namespace NormFormula.XY

noncomputable section

universe w

open NormFormula.ContinuousLogic

/-- The logical conclusions of the direct-sum corollary: the norm formula is
unstable but NIP on the distinguished direct sum, while it has IP in the
complete theory. -/
theorem normFormula_unstable_nip_and_theoryIP
    {SX : NormFormula.SequentialLocalNIPSemantics X.XSpace}
    {SY : NormFormula.SequentialLocalNIPSemantics HalfGraph.Y}
    {SXY : NormFormula.SequentialLocalNIPSemantics XYSpace}
    {SIP : NormFormula.CompleteTheoryIPSemantics XYSpace XYSpace}
    (PLocal : LocalNIPSumPresentation SX SY SXY)
    (PIP : CompleteTheoryIPPresentation SIP)
    (hx : SX.IsNIPOnDistinguished PLocal.xNormFormula)
    (hy : SY.IsNIPOnDistinguished PLocal.yNormFormula) :
    (¬ NormFormula.IsStableOnBounded
      (fun x y ↦ SXY.formulaValue PLocal.xyNormFormula
        x (PLocal.xyHomeParameter y))) ∧
      SXY.IsNIPOnDistinguished PLocal.xyNormFormula ∧
      SIP.IsIPInTheory PIP.normFormula := by
  have hvalue :
      (fun x y ↦ SXY.formulaValue PLocal.xyNormFormula
        x (PLocal.xyHomeParameter y)) = normTranslate := by
    funext x y
    exact PLocal.xyNormFormula_value x y
  refine ⟨?_, PLocal.normFormula_isNIPOnDistinguished hx hy,
    PIP.normFormula_isIPInCompleteTheory⟩
  intro hstable
  exact normTranslate_not_isStableOnBounded (hstable.congr hvalue)

/-- The logical direct-sum corollary in the concrete bounded-sorts continuous
syntax, with no presentation or factor-NIP hypotheses: the norm formula is
unstable on the home space, NIP on every positive ball sort, and IP in the
complete theory. -/
theorem normFormula_unstable_locallyNIP_and_theoryIP :
    (¬ NormFormula.IsStableOnBounded normTranslate) ∧
      NormFormulaIsNIPOnPositiveBalls XYSpace ∧
      NormFormulaHasIPInCompleteTheory XYSpace := by
  exact ⟨normTranslate_not_isStableOnBounded,
    fun R hR ↦ normAddMultiFormula_isNIPOnStructure R hR,
    normFormula_hasIPInSemanticCompleteTheory⟩

/-- The unconditional separability and quantitative geometric conclusions
for the concrete direct sum. -/
theorem verified_geometric_conclusions :
    TopologicalSpace.IsSeparable (Set.univ : Set XYSpace) ∧
      (∀ x y : XYSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤
          1 - (1 / 12 : ℝ) * ‖x - y‖ ^ 2) ∧
      (∀ z : XYSpace, ‖toHilbert z‖ ≤ ‖z‖) ∧
      (∀ z : XYHilbertSpace,
        ‖ofHilbert z‖ ≤ Real.sqrt 3 * ‖z‖) := by
  exact ⟨TopologicalSpace.isSeparable_univ_iff.mpr inferInstance,
    fun _ _ hx hy ↦ norm_midpoint_sq_le hx hy,
    norm_toHilbert_le, norm_ofHilbert_le⟩

end

end NormFormula.XY
