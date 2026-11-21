import NormFormula.ContinuousLogic.AbsoluteDifference
import NormFormula.ContinuousLogic.MultiTheoryIP

/-! # Identities of bounded predicates transfer with their complete theory -/
namespace NormFormula.ContinuousLogic
noncomputable section
namespace MultiFormula

theorem equivalentInCompleteTheory_of_binaryValue_eq
    {Symbol : Type*} {M : MultiStructure Symbol}
    (φ ψ : MultiFormula Symbol 1 1)
    (h : ∀ x y, φ.binaryValue M x y = ψ.binaryValue M x y) :
    EquivalentInCompleteTheory M φ ψ := by
  let discrepancy : MultiFormula Symbol 1 1 :=
    .connective absoluteDifferenceConnective ![φ, ψ]
  let sentence : MultiSentence Symbol := .iSupParameter (.iSupRow discrepancy)
  have hzero : sentence.value M = zeroTruthValue := by
    apply le_antisymm
    · apply iSup_le
      intro y
      apply iSup_le
      intro x
      change absoluteDifferenceConnective ![φ.realize M _ _, ψ.realize M _ _] ≤ _
      have hv := h x y
      change (φ.realize M (fun _ ↦ x) (fun _ ↦ y) : ℝ) =
        (ψ.realize M (fun _ ↦ x) (fun _ ↦ y) : ℝ) at hv
      have he : φ.realize M (Fin.cons x Fin.elim0) (Fin.cons y Fin.elim0) =
          ψ.realize M (Fin.cons x Fin.elim0) (Fin.cons y Fin.elim0) := by
        convert Subtype.ext hv using 1 <;> congr 1 <;> funext i <;> fin_cases i <;> rfl
      change |(_ : ℝ) - (_ : ℝ)| ≤ 0
      simp [he]
    · exact (sentence.value M).2.1
  intro N hTheory rows parameters
  have hn : sentence.value N = zeroTruthValue := (hTheory sentence).symm.trans hzero
  have hl : discrepancy.realize N rows parameters ≤ sentence.value N := by
    have hr : rows = Fin.cons (rows 0) Fin.elim0 := by funext i; fin_cases i; rfl
    have hp : parameters = Fin.cons (parameters 0) Fin.elim0 := by funext i; fin_cases i; rfl
    rw [hr, hp]
    exact (le_iSup (fun x ↦ discrepancy.realize N
      (Fin.cons x Fin.elim0) (Fin.cons (parameters 0) Fin.elim0)) (rows 0)).trans
      (le_iSup (fun y ↦ ⨆ x, discrepancy.realize N
        (Fin.cons x Fin.elim0) (Fin.cons y Fin.elim0)) (parameters 0))
  rw [hn] at hl
  apply Subtype.ext
  change |(φ.realize N rows parameters : ℝ) - (ψ.realize N rows parameters : ℝ)| ≤ 0 at hl
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hl (abs_nonneg _)))
end MultiFormula
end
end NormFormula.ContinuousLogic
