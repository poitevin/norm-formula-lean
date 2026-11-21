import NormFormula.Combinatorics.RealCutPartition
import NormFormula.Combinatorics.ThresholdTrace
import Mathlib.Data.Finset.Powerset

/-!
# Elementary counting of threshold traces

For each of the expressions `tᵢ` and `tᵢ+tⱼ`, record its piece in the
partition by the common real cut set. Counting all possible piece assignments
gives the paper's exponent `ℓ + choose ℓ 2` for a fixed order type. This proof
uses no hyperplane face-count theorem.
-/

namespace NormFormula.HalfGraph

def elementaryExpressionCount (ℓ : ℕ) : ℕ := ℓ + ℓ.choose 2

def elementaryVariableSets (ℓ : ℕ) : Finset (Finset (Fin ℓ)) :=
  Finset.univ.powersetCard 1 ∪ Finset.univ.powersetCard 2

theorem card_elementaryVariableSets_le (ℓ : ℕ) :
    (elementaryVariableSets ℓ).card ≤ elementaryExpressionCount ℓ := by
  have h := Finset.card_union_le (Finset.univ.powersetCard 1 : Finset (Finset (Fin ℓ)))
    (Finset.univ.powersetCard 2)
  simpa [elementaryVariableSets, elementaryExpressionCount, Finset.card_powersetCard] using h

noncomputable def elementaryCuts {ρ : Type*} [Fintype ρ]
    (constants : ρ → Finset ℝ) (threshold : ρ → ℝ) : Finset ℝ := by
  classical
  exact Finset.univ.biUnion fun r ↦
    (constants r).image (fun α ↦ threshold r - α) ∪
      (constants r).image (fun α ↦ -threshold r - α)

theorem card_elementaryCuts_le {ρ : Type*} [Fintype ρ]
    (constants : ρ → Finset ℝ) (threshold : ρ → ℝ) (M : ℕ)
    (hconstants : ∀ r, (constants r).card ≤ M) :
    (elementaryCuts constants threshold).card ≤ 2 * Fintype.card ρ * M := by
  classical
  have hrow (r : ρ) :
      ((constants r).image (fun α ↦ threshold r - α) ∪
        (constants r).image (fun α ↦ -threshold r - α)).card ≤ 2 * M := by
    exact (Finset.card_union_le _ _).trans
      ((Nat.add_le_add (Finset.card_image_le.trans (hconstants r))
        (Finset.card_image_le.trans (hconstants r))).trans_eq (by omega))
  have h := Finset.card_biUnion_le_card_mul Finset.univ _ (2 * M) (fun r _ ↦ hrow r)
  simpa [elementaryCuts, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

theorem abs_threshold_iff_of_cut_piece
    {ρ : Type*} [Fintype ρ] (constants : ρ → Finset ℝ) (threshold : ρ → ℝ)
    (r : ρ) {α x y : ℝ} (hα : α ∈ constants r)
    (hpiece : NormFormula.realCutPiece (elementaryCuts constants threshold) x =
      NormFormula.realCutPiece (elementaryCuts constants threshold) y) :
    (threshold r ≤ |α + x| ↔ threshold r ≤ |α + y|) := by
  classical
  have hcuts : threshold r - α ∈ elementaryCuts constants threshold ∧
      -threshold r - α ∈ elementaryCuts constants threshold := by
    constructor
    · exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ r,
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨α, hα, rfl⟩)⟩
    · exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ r,
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨α, hα, rfl⟩)⟩
  have hp := (NormFormula.realCutPiece_eq_comparisons hpiece hcuts.1).1
  have hm := (NormFormula.realCutPiece_eq_comparisons hpiece hcuts.2).2
  rw [le_abs, le_abs]
  constructor
  · rintro (h | h)
    · left; have := hp.mp (by linarith); linarith
    · right; have := hm.mp (by linarith); linarith
  · rintro (h | h)
    · left; have := hp.mpr (by linarith); linarith
    · right; have := hm.mpr (by linarith); linarith

/-- The exact elementary bound for finite affine lists whose variable parts
are sums of at most two distinct parameter coordinates. -/
theorem card_realizableRowThresholdTraces_le_elementary
    {ρ : Type*} [Fintype ρ] {ℓ M : ℕ}
    (forms : ρ → Finset (AffineForm ℓ)) (constants : ρ → Finset ℝ)
    (threshold : ρ → ℝ)
    (hconstants : ∀ r, (constants r).card ≤ M)
    (hforms : ∀ r f, f ∈ forms r → ∃ α ∈ constants r, ∃ s : Finset (Fin ℓ),
      s.card ≤ 2 ∧ ∀ t, f.eval t = α + ∑ a ∈ s, t a) :
    (realizableRowThresholdTraces forms threshold).card ≤
      (4 * Fintype.card ρ * M + 1) ^ elementaryExpressionCount ℓ := by
  classical
  let C := elementaryCuts constants threshold
  let W := elementaryVariableSets ℓ
  let record (t : Fin ℓ → ℝ) : W → NormFormula.RealCutPiece C :=
    fun s ↦ NormFormula.realCutPiece C (∑ a ∈ s.1, t a)
  have hdet (t u : Fin ℓ → ℝ) (heq : record t = record u) :
      rowThresholdTrace forms threshold t = rowThresholdTrace forms threshold u := by
    have htest (r : ρ) (f : forms r) :
        threshold r ≤ |f.1.eval t| ↔ threshold r ≤ |f.1.eval u| := by
      obtain ⟨α, hα, s, hs, hf⟩ := hforms r f.1 f.2
      rw [hf t, hf u]
      by_cases hempty : s = ∅
      · simp [hempty]
      · have hspos : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
        have hsW : s ∈ W := by
          have hcard : s.card = 1 ∨ s.card = 2 := by omega
          rcases hcard with hcard | hcard
          · exact Finset.mem_union_left _ (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩)
          · exact Finset.mem_union_right _ (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩)
        exact abs_threshold_iff_of_cut_piece constants threshold r hα
          (congrFun heq ⟨s, hsW⟩)
    ext r
    simp only [rowThresholdTrace, Finset.mem_filter, Finset.mem_univ, true_and]
    exact exists_congr (htest r)
  have hcard := NormFormula.card_traces_le_of_finite_record
    (rowThresholdTrace forms threshold) record hdet
  have hsame : NormFormula.realizedTraces (rowThresholdTrace forms threshold) =
      realizableRowThresholdTraces forms threshold := by
    ext s
    simp [NormFormula.realizedTraces, mem_realizableRowThresholdTraces]
  rw [hsame] at hcard
  have hbase : 2 * C.card + 1 ≤ 4 * Fintype.card ρ * M + 1 := by
    have hc := card_elementaryCuts_le constants threshold M hconstants
    dsimp [C]
    nlinarith
  calc
    _ ≤ (2 * C.card + 1) ^ W.card := by simpa only [Fintype.card_fun, NormFormula.card_realCutPiece, Fintype.card_coe] using hcard
    _ ≤ (4 * Fintype.card ρ * M + 1) ^ W.card := pow_le_pow_left' hbase _
    _ ≤ (4 * Fintype.card ρ * M + 1) ^ elementaryExpressionCount ℓ :=
      pow_le_pow_right' (by omega) (card_elementaryVariableSets_le ℓ)

end NormFormula.HalfGraph
