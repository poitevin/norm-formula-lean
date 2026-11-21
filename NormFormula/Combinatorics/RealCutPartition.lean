import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith

/-!
# Points and intervals determined by finitely many real cuts

The singleton cuts and the complementary open intervals give `2|C|+1`
pieces. Equal piece indices preserve both weak comparisons with each cut.
This is the one-dimensional partition used in Section 4.2 of the paper.
-/

namespace NormFormula

abbrev RealCutPiece (C : Finset ℝ) := C ⊕ Fin (C.card + 1)

noncomputable def realCutPiece (C : Finset ℝ) (x : ℝ) : RealCutPiece C := by
  classical
  exact if hx : x ∈ C then Sum.inl ⟨x, hx⟩ else
    Sum.inr ⟨(C.filter (· < x)).card,
      Nat.lt_succ_of_le (Finset.card_filter_le _ _)⟩

@[simp] theorem card_realCutPiece (C : Finset ℝ) :
    Fintype.card (RealCutPiece C) = 2 * C.card + 1 := by
  simp [RealCutPiece]
  omega

theorem realCutPiece_eq_comparisons {C : Finset ℝ} {x y c : ℝ}
    (h : realCutPiece C x = realCutPiece C y) (hc : c ∈ C) :
    (c ≤ x ↔ c ≤ y) ∧ (x ≤ c ↔ y ≤ c) := by
  classical
  by_cases hx : x ∈ C
  · have hy : y ∈ C := by
      by_contra hy
      simp [realCutPiece, hx, hy] at h
    have hxy : x = y := by simpa [realCutPiece, hx, hy] using h
    subst y
    exact ⟨Iff.rfl, Iff.rfl⟩
  · have hy : y ∉ C := by
      intro hy
      simp [realCutPiece, hx, hy] at h
    have hcard : (C.filter (· < x)).card = (C.filter (· < y)).card := by
      simpa [realCutPiece, hx, hy] using h
    have heq : C.filter (· < x) = C.filter (· < y) := by
      rcases le_total x y with hxy | hyx
      · exact Finset.eq_of_subset_of_card_le
          (by intro z hz; exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2.trans_le hxy⟩) hcard.ge
      · exact (Finset.eq_of_subset_of_card_le
          (by intro z hz; exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2.trans_le hyx⟩) hcard.le).symm
    have hlt : c < x ↔ c < y := by
      simpa [hc] using Finset.ext_iff.mp heq c
    have hxc : x ≠ c := fun hxc ↦ hx (hxc ▸ hc)
    have hyc : y ≠ c := fun hyc ↦ hy (hyc ▸ hc)
    constructor
    · constructor
      · intro hle
        exact (hlt.mp (lt_of_le_of_ne hle (Ne.symm hxc))).le
      · intro hle
        exact (hlt.mpr (lt_of_le_of_ne hle (Ne.symm hyc))).le
    · simpa only [not_lt] using not_congr hlt

noncomputable def realizedTraces {ρ T : Type*} [Fintype ρ]
    (trace : T → Finset ρ) : Finset (Finset ρ) := by
  classical
  exact Finset.univ.filter fun s ↦ ∃ t, trace t = s

/-- A finite record determining every trace bounds the number of traces by
the number of records, whether or not all records are realizable. -/
theorem card_traces_le_of_finite_record
    {ρ T Code : Type*} [Fintype ρ] [Fintype Code]
    (trace : T → Finset ρ) (record : T → Code)
    (hdet : ∀ t u, record t = record u → trace t = trace u) :
    (realizedTraces trace).card ≤ Fintype.card Code := by
  classical
  let traces := Finset.univ.filter fun s : Finset ρ ↦ ∃ t, trace t = s
  have hw (s : traces) : ∃ t, trace t = s.1 := (Finset.mem_filter.mp s.2).2
  let witness (s : traces) := Classical.choose (hw s)
  have hinj : Function.Injective (fun s : traces ↦ record (witness s)) := by
    intro s v h
    apply Subtype.ext
    have heq := hdet (witness s) (witness v) h
    simpa [witness, Classical.choose_spec (hw s), Classical.choose_spec (hw v)] using heq
  have hcard := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_coe] at hcard
  exact hcard

end NormFormula
