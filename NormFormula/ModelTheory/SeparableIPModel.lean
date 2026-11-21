import Mathlib.Topology.Sequences
import NormFormula.ModelTheory.LocalNIP

/-!
# Extracting a separable model with an infinite IP witness

The final section of the paper uses continuous compactness followed by
downward Löwenheim--Skolem. Uniform finite patterns in the home model produce
a separable model of its complete theory containing one infinite independent
row sequence.

Mathlib has no continuous first-order syntax or compactness theorem, so the
compactness/LS step is isolated in an explicit semantic interface. The shape
of the resulting bounded infinite witness is defined concretely here.
-/

namespace NormFormula

/-- A single bounded row sequence realizes every finite low/high pattern.
This is the paper's notion of IP on one distinguished model. -/
def HasBoundedInfiniteIPWitness
    {X Y : Type*} [Norm X] [Norm Y]
    (value : X → Y → ℝ) (R_x R_y low high : ℝ) : Prop :=
  ∃ rows : ℕ → X,
    (∀ i, ‖rows i‖ ≤ R_x) ∧
      ∀ E F : Finset ℕ, Disjoint E F →
        ∃ b : Y, ‖b‖ ≤ R_y ∧
          (∀ i ∈ E, value (rows i) b ≤ low) ∧
          (∀ i ∈ F, high ≤ value (rows i) b)

namespace HasBoundedInfiniteIPWitness

/-- Infinite IP witnesses depend only on the pointwise interpretation. -/
theorem congr
    {X Y : Type*} [Norm X] [Norm Y]
    {value value' : X → Y → ℝ} {R_x R_y low high : ℝ}
    (h : HasBoundedInfiniteIPWitness value R_x R_y low high)
    (hvalue : value = value') :
    HasBoundedInfiniteIPWitness value' R_x R_y low high := by
  subst value'
  exact h

end HasBoundedInfiniteIPWitness

universe u v w

/-- Syntax-free semantic data for a candidate Banach model `W` of the home
theory.  The compactness/LS extraction obligation is deliberately kept out of
this structure: it must be stated for the particular formula and finite
pattern used to choose `W`, rather than universally for every formula on one
preselected separable model. -/
structure SeparableIPModelSemantics
    (X : Type u) (W : Type v) [Norm X]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] where
  Formula : Type w
  homeValue : Formula → X → X → ℝ
  modelValue : Formula → W → W → ℝ
  IsModelOfHomeTheory : Prop

namespace SeparableIPModelSemantics

variable {X : Type u} {W : Type v} [Norm X]
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- The exact continuous-compactness and downward-Löwenheim--Skolem
obligation for one named formula, one fixed choice of bounds and thresholds,
and the particular extracted model `W`.

Keeping this proposition formula-specific matches the manuscript: `W` is
chosen only after the norm formula and its fixed cube patterns have been
specified. -/
def ExtractsSeparableIPModel
    (S : SeparableIPModelSemantics X W) (φ : S.Formula)
    (R_x R_y low high : ℝ) : Prop :=
    low < high →
    HasIPPatternsInEveryDimension
      (S.homeValue φ) R_x R_y low high →
    S.IsModelOfHomeTheory ∧
      TopologicalSpace.IsSeparable (Set.univ : Set W) ∧
      HasBoundedInfiniteIPWitness
        (S.modelValue φ) R_x R_y low high

variable (S : SeparableIPModelSemantics X W)

/-- A convenient form allowing the home and extracted-model interpretations
to be named separately from the abstract formula token. -/
theorem extract_of_value_eq_of_finitePatterns
    (φ : S.Formula)
    (homeValue : X → X → ℝ) (modelValue : W → W → ℝ)
    (hhome : S.homeValue φ = homeValue)
    (hmodel : S.modelValue φ = modelValue)
    (R_x R_y low high : ℝ)
    (hextract : S.ExtractsSeparableIPModel φ R_x R_y low high)
    (hgap : low < high)
    (hpatterns : HasIPPatternsInEveryDimension
      homeValue R_x R_y low high) :
    S.IsModelOfHomeTheory ∧
      TopologicalSpace.IsSeparable (Set.univ : Set W) ∧
      HasBoundedInfiniteIPWitness modelValue R_x R_y low high := by
  have h := hextract hgap (by simpa [hhome] using hpatterns)
  exact ⟨h.1, h.2.1, h.2.2.congr hmodel⟩

end SeparableIPModelSemantics

end NormFormula
