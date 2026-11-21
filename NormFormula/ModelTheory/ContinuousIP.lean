import NormFormula.ModelTheory.LocalNIP

/-!
# A syntax-free compactness interface for theory-level IP

Mathlib does not currently provide continuous first-order compactness.  This
module isolates the one direction used for the paper's space `X`: bounded
fixed-gap IP patterns in every finite dimension of the distinguished model
produce IP for the corresponding formula in its complete theory.

The compactness statement is a field of an explicit structure.  It is not
declared as a Lean axiom or global instance.
-/

namespace NormFormula

universe u v w

/-- The minimal semantic data needed to turn uniform finite patterns in one
distinguished normed structure into IP in its complete continuous theory. -/
structure CompleteTheoryIPSemantics (X : Type u) (Y : Type v)
    [Norm X] [Norm Y] where
  Formula : Type w
  formulaValue : Formula → X → Y → ℝ
  IsIPInTheory : Formula → Prop
  finitePatternsToTheoryIP : ∀ φ R_x R_y low high,
    low < high →
    HasIPPatternsInEveryDimension
      (formulaValue φ) R_x R_y low high →
    IsIPInTheory φ

namespace CompleteTheoryIPSemantics

variable {X : Type u} {Y : Type v} [Norm X] [Norm Y]
variable (S : CompleteTheoryIPSemantics X Y)

/-- A convenient form allowing the concrete interpretation to be named
separately from the abstract formula token. -/
theorem isIPInTheory_of_value_eq_of_finitePatterns
    (φ : S.Formula) (value : X → Y → ℝ)
    (hvalue : S.formulaValue φ = value)
    (R_x R_y low high : ℝ) (hgap : low < high)
    (hpatterns : HasIPPatternsInEveryDimension
      value R_x R_y low high) :
    S.IsIPInTheory φ := by
  apply S.finitePatternsToTheoryIP φ R_x R_y low high hgap
  rw [hvalue]
  exact hpatterns

end CompleteTheoryIPSemantics

end NormFormula
