import NormFormula.ContinuousLogic.BanachBallFormula

/-!
# Independence witnesses in the typed ball language

This file supplies the semantic IP notions needed for compactness in the
many-sorted rational-ball syntax.  A binary formula has one specified row
radius and parameter radius; all norm bounds are therefore built into its
two sorts.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u w

namespace BallFormula

/-- Evaluation of a two-variable typed formula on its row and parameter
sorts. -/
def binaryValue
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {rowRadius parameterRadius : ℚ≥0}
    (formula : BallFormula Symbol symbolRadius
      (![rowRadius, parameterRadius] : BallContext 2))
    (M : BallStructure.{u, w} Symbol symbolRadius)
    (row : M.Ball rowRadius) (parameter : M.Ball parameterRadius) : ℝ :=
  (formula.realize M
    (Fin.cons row (Fin.cons parameter (fun i : Fin 0 ↦ nomatch i))) : ℝ)

/-- One infinite fixed-gap independence witness for a typed binary ball
formula. -/
def HasInfiniteIPWitness
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {rowRadius parameterRadius : ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius)
    (formula : BallFormula Symbol symbolRadius
      (![rowRadius, parameterRadius] : BallContext 2))
    (low high : ℝ) : Prop :=
  ∃ rows : ℕ → M.Ball rowRadius,
    ∀ E F : Finset ℕ, Disjoint E F →
      ∃ parameter : M.Ball parameterRadius,
        (∀ i ∈ E, formula.binaryValue M (rows i) parameter ≤ low) ∧
        (∀ i ∈ F, high ≤ formula.binaryValue M (rows i) parameter)

/-- A typed binary ball formula has IP in the complete theory of `M` when an
infinite fixed-gap witness exists in a same-complete-theory ball structure. -/
def HasIPInCompleteTheory
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {rowRadius parameterRadius : ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius)
    (formula : BallFormula Symbol symbolRadius
      (![rowRadius, parameterRadius] : BallContext 2)) : Prop :=
  ∃ N : BallStructure.{u, w} Symbol symbolRadius,
    BallSameCompleteTheory M N ∧
      ∃ low high : ℝ, low < high ∧
        formula.HasInfiniteIPWitness N low high

/-- Semantic NIP for a typed binary formula in a complete ball theory. -/
def IsNIPInCompleteTheory
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {rowRadius parameterRadius : ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius)
    (formula : BallFormula Symbol symbolRadius
      (![rowRadius, parameterRadius] : BallContext 2)) : Prop :=
  ¬ formula.HasIPInCompleteTheory M

/-- Fixed-gap finite patterns in every dimension for one typed binary ball
formula. -/
def HasFiniteIPPatternsInEveryDimension
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {rowRadius parameterRadius : ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius)
    (formula : BallFormula Symbol symbolRadius
      (![rowRadius, parameterRadius] : BallContext 2))
    (low high : ℝ) : Prop :=
  ∀ n : ℕ, ∃ rows : Fin n → M.Ball rowRadius,
    NormFormula.IsIPPattern
      (fun i parameter ↦ formula.binaryValue M (rows i) parameter)
      low high

/-- The exact compactness implication required by the typed ball fragment. -/
def FinitePatternCompactness
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius) : Prop :=
  ∀ {rowRadius parameterRadius : ℚ≥0}
    (formula : BallFormula Symbol symbolRadius
      (![rowRadius, parameterRadius] : BallContext 2))
    (low high : ℝ), low < high →
      formula.HasFiniteIPPatternsInEveryDimension M low high →
      formula.HasIPInCompleteTheory M

end BallFormula

end

end NormFormula.ContinuousLogic
