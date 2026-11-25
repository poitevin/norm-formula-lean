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


variable (S : SeparableIPModelSemantics X W)


end SeparableIPModelSemantics

end NormFormula
