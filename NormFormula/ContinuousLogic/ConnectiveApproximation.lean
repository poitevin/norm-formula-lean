import Mathlib.Topology.UniformSpace.HeineCantor
import NormFormula.ContinuousLogic.QuantifierApproximation

/-!
# Uniform coordinatewise tolerances for bounded connectives

Every continuous connective is uniformly continuous on its compact finite
truth-value cube.  This file extracts the coordinatewise input tolerance
needed to propagate approximation errors through a connective node in the
structural formula-density induction.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

namespace Connective

/-- A bounded continuous connective is uniformly continuous because its
finite truth-value cube is compact. -/
theorem uniformContinuous {arity : ℕ} (connective : Connective arity) :
    UniformContinuous connective :=
  CompactSpace.uniformContinuous_of_continuous connective.continuous_toFun

/-- Every positive output error for a bounded connective admits one positive
input tolerance that works coordinatewise in all finitely many coordinates. -/
theorem exists_coordinatewise_tolerance {arity : ℕ}
    (connective : Connective arity) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ first second : Fin arity → TruthValue,
      (∀ coordinate,
        |(first coordinate : ℝ) - (second coordinate : ℝ)| < δ) →
      |(connective first : ℝ) - (connective second : ℝ)| < ε := by
  obtain ⟨δ, hδ, hmodulus⟩ :=
    Metric.uniformContinuous_iff.mp connective.uniformContinuous ε hε
  refine ⟨δ, hδ, fun first second hcoordinates => ?_⟩
  have hdist : dist first second < δ := by
    rw [dist_pi_lt_iff hδ]
    intro coordinate
    simpa [Real.dist_eq] using hcoordinates coordinate
  simpa [Real.dist_eq] using hmodulus hdist

end Connective

end

end NormFormula.ContinuousLogic
