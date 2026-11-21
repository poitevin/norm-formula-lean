import NormFormula.Combinatorics.FatShattering
import Mathlib.Combinatorics.Pigeonhole

/-!
# Finite independence patterns

This file formalizes the elementary finite-pattern bridge used in the paper:
a fixed low/high gap is a fat-shattering margin after placing every threshold
at the midpoint of that gap.
-/

namespace NormFormula

/-- A finite independence pattern with common low and high thresholds.
Membership in `S` means a high value, and nonmembership means a low value. -/
def IsIPPattern {ρ β : Type*} [Fintype ρ]
    (value : ρ → β → ℝ) (low high : ℝ) : Prop :=
  ∀ S : Finset ρ, ∃ b : β,
    (∀ r ∈ S, high ≤ value r b) ∧
    (∀ r ∉ S, value r b ≤ low)

/-- A fixed-gap IP pattern fat-shatters the rows at every margin no larger
than half of the gap.  All row thresholds are the common midpoint. -/
theorem IsIPPattern.isFatShattered
    {ρ β : Type*} [Fintype ρ] {value : ρ → β → ℝ}
    {low high ε : ℝ} (hip : IsIPPattern value low high)
    (hmargin : ε ≤ (high - low) / 2) :
    IsFatShattered value ε := by
  refine ⟨fun _ ↦ (high + low) / 2, ?_⟩
  intro S
  obtain ⟨b, hin, hout⟩ := hip S
  refine ⟨b, ?_, ?_⟩
  · intro r hr
    have hhigh := hin r hr
    dsimp
    linarith
  · intro r hr
    have hlow := hout r hr
    dsimp
    linarith

/-- In particular, the exact half-gap is a valid fat-shattering margin. -/
theorem IsIPPattern.isFatShattered_halfGap
    {ρ β : Type*} [Fintype ρ] {value : ρ → β → ℝ}
    {low high : ℝ} (hip : IsIPPattern value low high) :
    IsFatShattered value ((high - low) / 2) :=
  hip.isFatShattered le_rfl

/-- Fat-shattering is inherited by restriction along an embedding of the row
index type. -/
theorem IsFatShattered.comp_embedding
    {ρ ρ' β : Type*} [Fintype ρ] [Fintype ρ']
    {value : ρ → β → ℝ} {ε : ℝ}
    (hfat : IsFatShattered value ε) (embedding : ρ' ↪ ρ) :
    IsFatShattered (fun r b ↦ value (embedding r) b) ε := by
  classical
  obtain ⟨threshold, hthreshold⟩ := hfat
  refine ⟨fun r ↦ threshold (embedding r), ?_⟩
  intro S
  obtain ⟨b, hin, hout⟩ := hthreshold (S.map embedding)
  refine ⟨b, ?_, ?_⟩
  · intro r hr
    exact hin (embedding r) (Finset.mem_map.mpr ⟨r, hr, rfl⟩)
  · intro r hr
    apply hout (embedding r)
    simpa using hr

/-- If all row thresholds of one fat-shattering witness lie in an interval
whose width is at most the margin, the same rows form a common-threshold IP
pattern. -/
theorem isIPPattern_of_fat_witness_of_threshold_band
    {ρ β : Type*} [Fintype ρ]
    {value : ρ → β → ℝ} {threshold : ρ → ℝ}
    {ε base width : ℝ}
    (hfat : ∀ S : Finset ρ, ∃ b : β,
      (∀ r ∈ S, threshold r + ε ≤ value r b) ∧
      (∀ r ∉ S, value r b ≤ threshold r - ε))
    (hband : ∀ r, base ≤ threshold r ∧ threshold r ≤ base + width) :
    IsIPPattern value (base + width - ε) (base + ε) := by
  intro S
  obtain ⟨b, hin, hout⟩ := hfat S
  refine ⟨b, ?_, ?_⟩
  · intro r hr
    linarith [(hband r).1, hin r hr]
  · intro r hr
    linarith [(hband r).2, hout r hr]

/-- In the equal-width case, banding fat-shattering thresholds in an interval
of width `ε` produces an IP pattern with the simple common thresholds
`base < base + ε`. -/
theorem isIPPattern_of_fat_witness_of_threshold_band_self
    {ρ β : Type*} [Fintype ρ]
    {value : ρ → β → ℝ} {threshold : ρ → ℝ}
    {ε base : ℝ}
    (hfat : ∀ S : Finset ρ, ∃ b : β,
      (∀ r ∈ S, threshold r + ε ≤ value r b) ∧
      (∀ r ∉ S, value r b ≤ threshold r - ε))
    (hband : ∀ r, base ≤ threshold r ∧ threshold r ≤ base + ε) :
    IsIPPattern value base (base + ε) := by
  simpa using isIPPattern_of_fat_witness_of_threshold_band
    hfat (width := ε) hband

/-- Finite threshold banding plus pigeonhole: if a fat-shattered row family
is large compared with the number of threshold bands, one band contains a
prescribed number of rows, and those rows form a common-threshold IP pattern.
This is the bridge from fixed-gap local NIP to bounded fat-shattering
dimension. -/
theorem exists_ipPattern_restriction_of_fat_witness_finite_banding
    {ρ κ β : Type*} [Fintype ρ] [Fintype κ] [Nonempty κ]
    {value : ρ → β → ℝ} {threshold : ρ → ℝ} {ε : ℝ}
    (hfat : ∀ S : Finset ρ, ∃ b : β,
      (∀ r ∈ S, threshold r + ε ≤ value r b) ∧
      (∀ r ∉ S, value r b ≤ threshold r - ε))
    (color : ρ → κ) (base : κ → ℝ)
    (hband : ∀ r, base (color r) ≤ threshold r ∧
      threshold r ≤ base (color r) + ε)
    {N : ℕ} (hcard : Fintype.card κ * N ≤ Fintype.card ρ) :
    ∃ k : κ, ∃ embedding : Fin N ↪ ρ,
      IsIPPattern (fun i b ↦ value (embedding i) b)
        (base k) (base k + ε) := by
  classical
  obtain ⟨k, hk⟩ := Fintype.exists_le_card_fiber_of_mul_le_card
    (f := color) hcard
  let fiber : Finset ρ := Finset.univ.filter fun r ↦ color r = k
  have hk' : N ≤ fiber.card := by
    simpa [fiber] using hk
  obtain ⟨embedding, hembedding⟩ :=
    Function.Embedding.exists_of_card_le_finset
      (α := Fin N) (s := fiber) (by simpa using hk')
  have hcolor : ∀ i, color (embedding i) = k := by
    intro i
    have hi := hembedding (Set.mem_range_self i)
    simpa [fiber] using hi
  refine ⟨k, embedding, ?_⟩
  apply isIPPattern_of_fat_witness_of_threshold_band_self
    (threshold := fun i ↦ threshold (embedding i))
  · intro S
    obtain ⟨b, hin, hout⟩ := hfat (S.map embedding)
    refine ⟨b, ?_, ?_⟩
    · intro i hi
      exact hin (embedding i) (Finset.mem_map.mpr ⟨i, hi, rfl⟩)
    · intro i hi
      apply hout (embedding i)
      simpa using hi
  · intro i
    simpa [hcolor i] using hband (embedding i)

end NormFormula
