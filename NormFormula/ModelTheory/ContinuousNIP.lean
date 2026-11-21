import NormFormula.ModelTheory.ConnectiveClosure

/-!
# A syntax-free interface for complete-theory NIP

Mathlib does not currently contain continuous first-order syntax and
compactness.  This module therefore records the exact semantic data used by
the manuscript's complete-theory argument.  Formulae are abstract tokens with
an interpretation in one distinguished normed structure.  The fields of
`ContinuousNIPSemantics` are proof obligations, not axioms or instances.

The four model-theoretic ingredients are kept separate:

* finite-pattern bounds in the distinguished structure transfer to NIP in its
  complete expanded theory;
* uniformly continuous connectives preserve theory-level NIP;
* NIP is invariant under equivalence in the expanded theory; and
* a reduct-language formula which is NIP in the expansion is NIP in the
  reduct.
-/

namespace NormFormula

universe u v w z

/-- The minimal semantic interface needed to pass from the proved bounded
finite-pattern statements to complete-theory NIP.

`ExpansionFormula` and `ReductFormula` stand for formula syntax.  Their
interpretations are only required on the distinguished structure because that
is where the concrete analytic and combinatorial estimates live.
`ExpansionEquivalent` represents equality of formulae in every model of the
complete expanded theory. -/
structure ContinuousNIPSemantics (X : Type u) (Y : Type v)
    [Norm X] [Norm Y] where
  ExpansionFormula : Type w
  ReductFormula : Type z
  expansionValue : ExpansionFormula → X → Y → ℝ
  reductValue : ReductFormula → X → Y → ℝ
  liftReduct : ReductFormula → ExpansionFormula
  liftReduct_value : ∀ φ,
    expansionValue (liftReduct φ) = reductValue φ
  connective₂ : (ℝ → ℝ → ℝ) →
    ExpansionFormula → ExpansionFormula → ExpansionFormula
  connective₂_value : ∀ F φ ψ,
    expansionValue (connective₂ F φ ψ) =
      fun x y ↦ F (expansionValue φ x y) (expansionValue ψ x y)
  ExpansionEquivalent : ExpansionFormula → ExpansionFormula → Prop
  IsNIPInExpansion : ExpansionFormula → Prop
  IsNIPInReduct : ReductFormula → Prop
  finitePatternTransfer : ∀ φ,
    IsBoundedOnNormBalls (expansionValue φ) →
    IsBoundedLocalNIP (expansionValue φ) →
    IsNIPInExpansion φ
  connectiveClosure₂ : ∀ F,
    UniformContinuous (fun p : ℝ × ℝ ↦ F p.1 p.2) →
    ∀ φ ψ,
      IsBoundedOnNormBalls (expansionValue φ) →
      IsBoundedOnNormBalls (expansionValue ψ) →
      IsNIPInExpansion φ → IsNIPInExpansion ψ →
      IsNIPInExpansion (connective₂ F φ ψ)
  nip_of_equivalent : ∀ {φ ψ},
    ExpansionEquivalent φ ψ → IsNIPInExpansion ψ →
      IsNIPInExpansion φ
  reductTransfer : ∀ φ,
    IsNIPInExpansion (liftReduct φ) → IsNIPInReduct φ

namespace ContinuousNIPSemantics

variable {X : Type u} {Y : Type v} [Norm X] [Norm Y]
variable (S : ContinuousNIPSemantics X Y)

/-- Two bounded-local-NIP interpretations give an NIP connective formula in
the complete expanded theory.  This combines only the explicitly named
finite-transfer and connective-closure fields. -/
theorem connective₂_isNIPInExpansion_of_local
    (F : ℝ → ℝ → ℝ)
    (hF : UniformContinuous fun p : ℝ × ℝ ↦ F p.1 p.2)
    (φ ψ : S.ExpansionFormula)
    (hφBounded : IsBoundedOnNormBalls (S.expansionValue φ))
    (hψBounded : IsBoundedOnNormBalls (S.expansionValue ψ))
    (hφLocal : IsBoundedLocalNIP (S.expansionValue φ))
    (hψLocal : IsBoundedLocalNIP (S.expansionValue ψ)) :
    S.IsNIPInExpansion (S.connective₂ F φ ψ) := by
  exact S.connectiveClosure₂ F hF φ ψ hφBounded hψBounded
    (S.finitePatternTransfer φ hφBounded hφLocal)
    (S.finitePatternTransfer ψ hψBounded hψLocal)

/-- If a reduct formula is equivalent in the expansion to a connective of
two locally controlled formulae, then it is NIP in the complete reduct
theory. -/
theorem reduct_isNIP_of_equivalent_connective_of_local
    (F : ℝ → ℝ → ℝ)
    (hF : UniformContinuous fun p : ℝ × ℝ ↦ F p.1 p.2)
    (φ ψ : S.ExpansionFormula) (θ : S.ReductFormula)
    (hφBounded : IsBoundedOnNormBalls (S.expansionValue φ))
    (hψBounded : IsBoundedOnNormBalls (S.expansionValue ψ))
    (hφLocal : IsBoundedLocalNIP (S.expansionValue φ))
    (hψLocal : IsBoundedLocalNIP (S.expansionValue ψ))
    (hequiv : S.ExpansionEquivalent (S.liftReduct θ)
      (S.connective₂ F φ ψ)) :
    S.IsNIPInReduct θ := by
  apply S.reductTransfer θ
  apply S.nip_of_equivalent hequiv
  exact S.connective₂_isNIPInExpansion_of_local F hF φ ψ
    hφBounded hψBounded hφLocal hψLocal

end ContinuousNIPSemantics

end NormFormula
