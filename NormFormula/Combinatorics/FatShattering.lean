import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Fat-shattering and finite threshold traces

This file isolates the elementary counting argument used in the paper.  If a
family fat-shatters `n` rows with margin `ε`, and a second family approximates
it with error strictly below `ε`, then the approximating threshold traces
contain all `2^n` subsets of the rows.  We also record that an exponential
eventually dominates every fixed polynomial.
-/

namespace NormFormula

open Filter

/-- The threshold trace of one parameter on a finite family of rows. -/
noncomputable def thresholdTrace {ρ β : Type*} [Fintype ρ]
    (value : ρ → β → ℝ) (threshold : ρ → ℝ) (b : β) : Finset ρ := by
  classical
  exact Finset.univ.filter fun r ↦ threshold r ≤ value r b

/-- A finite indexed family is `ε`-fat-shattered when every subset can be
separated from row-dependent thresholds by the two-sided margin `ε`. -/
def IsFatShattered {ρ β : Type*} [Fintype ρ]
    (value : ρ → β → ℝ) (ε : ℝ) : Prop :=
  ∃ threshold : ρ → ℝ, ∀ S : Finset ρ, ∃ b : β,
    (∀ r ∈ S, threshold r + ε ≤ value r b) ∧
    (∀ r ∉ S, value r b ≤ threshold r - ε)

/-- Fat-shattering is monotone under a value-preserving map from the witness
parameter type into a larger parameter type. -/
theorem IsFatShattered.reparam
    {ρ SmallParameter LargeParameter : Type*} [Fintype ρ]
    {smallValue : ρ → SmallParameter → ℝ}
    {largeValue : ρ → LargeParameter → ℝ} {ε : ℝ}
    (hfat : IsFatShattered smallValue ε)
    (parameterMap : SmallParameter → LargeParameter)
    (hvalue : ∀ row parameter,
      largeValue row (parameterMap parameter) = smallValue row parameter) :
    IsFatShattered largeValue ε := by
  obtain ⟨threshold, hthreshold⟩ := hfat
  refine ⟨threshold, ?_⟩
  intro S
  obtain ⟨parameter, hhigh, hlow⟩ := hthreshold S
  refine ⟨parameterMap parameter, ?_, ?_⟩
  · intro row hrow
    rw [hvalue]
    exact hhigh row hrow
  · intro row hrow
    rw [hvalue]
    exact hlow row hrow


/-- Strict approximation within the fat-shattering margin preserves the
subset encoded by every witness as an ordinary threshold trace. -/
theorem thresholdTrace_eq_of_fat_witness
    {ρ β γ : Type*} [Fintype ρ]
    {value : ρ → β → ℝ} {approxValue : ρ → γ → ℝ}
    {threshold : ρ → ℝ} {ε : ℝ} {S : Finset ρ} {b : β} {g : γ}
    (hin : ∀ r ∈ S, threshold r + ε ≤ value r b)
    (hout : ∀ r ∉ S, value r b ≤ threshold r - ε)
    (happrox : ∀ r, |value r b - approxValue r g| < ε) :
    thresholdTrace approxValue threshold g = S := by
  classical
  ext r
  simp only [thresholdTrace, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hr
    by_contra hrs
    have hlow := hout r hrs
    have habs := (abs_lt.mp (happrox r)).1
    linarith
  · intro hrs
    have hhigh := hin r hrs
    have habs := (abs_lt.mp (happrox r)).2
    linarith

/-- Counting lemma with the shattering thresholds exposed.  This form is
useful when the finite trace cover itself depends on those thresholds. -/
theorem two_pow_card_le_trace_cover_of_fat_witness
    {ρ β γ : Type*} [Fintype ρ]
    {value : ρ → β → ℝ} {approxValue : ρ → γ → ℝ}
    {approx : β → γ} {threshold : ρ → ℝ} {ε : ℝ}
    {traces : Finset (Finset ρ)}
    (hfat : ∀ S : Finset ρ, ∃ b : β,
      (∀ r ∈ S, threshold r + ε ≤ value r b) ∧
      (∀ r ∉ S, value r b ≤ threshold r - ε))
    (herror : ∀ r b, |value r b - approxValue r (approx b)| < ε)
    (hcover : ∀ b, thresholdTrace approxValue threshold (approx b) ∈ traces) :
    2 ^ Fintype.card ρ ≤ traces.card := by
  classical
  have huniv : (Finset.univ : Finset (Finset ρ)) ⊆ traces := by
    intro S _
    obtain ⟨b, hin, hout⟩ := hfat S
    rw [← thresholdTrace_eq_of_fat_witness hin hout (herror · b)]
    exact hcover b
  have hcard := Finset.card_le_card huniv
  simpa [Fintype.card_finset] using hcard


/-- For fixed natural constants `C` and `d`, `C(n+1)^d` is eventually
strictly smaller than `2^n`. -/
theorem eventually_polynomial_lt_two_pow (C d : ℕ) :
    ∀ᶠ n : ℕ in atTop, C * (n + 1) ^ d < 2 ^ n := by
  have hden : 0 < 2 * ((C : ℝ) + 1) := by positivity
  have hlimit := tendsto_pow_const_div_const_pow_of_one_lt d
    (by norm_num : (1 : ℝ) < 2)
  have hevent : ∀ᶠ m : ℕ in atTop,
      (m : ℝ) ^ d / 2 ^ m < (2 * ((C : ℝ) + 1))⁻¹ :=
    hlimit.eventually (gt_mem_nhds (inv_pos.mpr hden))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' := hN (n + 1) (hn.trans (Nat.le_succ n))
  have hpowpos : 0 < (2 : ℝ) ^ (n + 1) := by positivity
  have hlt : ((n + 1 : ℕ) : ℝ) ^ d <
      (2 * ((C : ℝ) + 1))⁻¹ * (2 : ℝ) ^ (n + 1) :=
    (div_lt_iff₀ hpowpos).mp hn'
  have hnonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ d := by positivity
  have hscale := mul_lt_mul_of_pos_left hlt (show 0 < (C : ℝ) + 1 by positivity)
  have hmain : (C : ℝ) * ((n + 1 : ℕ) : ℝ) ^ d < (2 : ℝ) ^ n := by
    calc
      (C : ℝ) * ((n + 1 : ℕ) : ℝ) ^ d ≤
          ((C : ℝ) + 1) * ((n + 1 : ℕ) : ℝ) ^ d := by
        nlinarith
      _ < ((C : ℝ) + 1) *
          ((2 * ((C : ℝ) + 1))⁻¹ * (2 : ℝ) ^ (n + 1)) := hscale
      _ = (2 : ℝ) ^ n := by
        rw [pow_succ]
        field_simp
  exact_mod_cast hmain

/-- Pointwise form of exponential domination, convenient for bounding
shattered row counts. -/
theorem exists_polynomial_lt_two_pow_bound (C d : ℕ) :
    ∃ N : ℕ, ∀ n, N ≤ n → C * (n + 1) ^ d < 2 ^ n :=
  eventually_atTop.mp (eventually_polynomial_lt_two_pow C d)

end NormFormula
