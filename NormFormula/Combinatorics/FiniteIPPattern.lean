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


end NormFormula
