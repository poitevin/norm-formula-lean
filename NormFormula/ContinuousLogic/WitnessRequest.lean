import Mathlib.Tactic.DeriveEncodable
import NormFormula.ContinuousLogic.QuantifierWitness

/-! Quantifier direction and precision for approximate witnesses. -/

namespace NormFormula.ContinuousLogic

noncomputable section

/-- Whether an approximate witness approaches a supremum from below or an
infimum from above. -/
inductive QuantifierDirection where
  | supremum
  | infimum
  deriving Encodable, DecidableEq

/-- The positive error assigned to a natural-number precision request. -/
def witnessError (precision : ℕ) : ℝ :=
  1 / ((precision : ℝ) + 1)

theorem witnessError_pos (precision : ℕ) :
    0 < witnessError precision := by
  unfold witnessError
  positivity

end

end NormFormula.ContinuousLogic
