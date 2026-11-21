import NormFormula.ModelTheory.BoundedStability
import NormFormula.ContinuousLogic.MultiTheoryIP
import NormFormula.ContinuousLogic.BanachBallTheoryIP

/-! # Formula stability on fixed sorts and in complete theories

These predicates use precisely the paper's double-limit condition. They
concern a specified formula, not stability of every formula in a theory.
-/
namespace NormFormula.ContinuousLogic
universe u v w

namespace MultiFormula

def IsStableOnStructure {Symbol : Type w} (M : MultiStructure.{u,v,w} Symbol)
    (φ : MultiFormula Symbol 1 1) : Prop :=
  IsStableKernel (φ.binaryValue M)

def IsStableInCompleteTheory {Symbol : Type w} (M : MultiStructure.{u,v,w} Symbol)
    (φ : MultiFormula Symbol 1 1) : Prop :=
  ∀ N : MultiStructure.{u,v,w} Symbol, MultiSameCompleteTheory M N →
    IsStableOnStructure N φ

end MultiFormula

namespace BallFormula

def IsStableOnStructure {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {r s : ℚ≥0} (M : BallStructure.{u,w} Symbol symbolRadius)
    (φ : BallFormula Symbol symbolRadius (![r,s] : BallContext 2)) : Prop :=
  IsStableKernel (φ.binaryValue M)

def IsStableInCompleteTheory {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {r s : ℚ≥0} (M : BallStructure.{u,w} Symbol symbolRadius)
    (φ : BallFormula Symbol symbolRadius (![r,s] : BallContext 2)) : Prop :=
  ∀ N : BallStructure.{u,w} Symbol symbolRadius, BallSameCompleteTheory M N →
    IsStableOnStructure N φ

end BallFormula
end NormFormula.ContinuousLogic
