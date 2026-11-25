import Mathlib.Logic.Encodable.Pi
import Mathlib.Tactic.DeriveEncodable
import NormFormula.ContinuousLogic.MultiPredicate

/-! Rational truth values and connectives for the countable Banach-ball syntax. -/

namespace NormFormula.ContinuousLogic

noncomputable section

open scoped Topology

universe w

/-- Clamp a real number to the truth-value interval `[0,1]`. -/
def clampTruthValue (x : ℝ) : TruthValue :=
  ⟨max 0 (min 1 x),
    le_max_left _ _,
    max_le zero_le_one (min_le_left _ _)⟩


/-- Clamping is continuous. -/
theorem continuous_clampTruthValue : Continuous clampTruthValue := by
  apply Continuous.subtype_mk
  exact continuous_const.max (continuous_const.min continuous_id)

/-- A rational affine function of two truth values, clipped back to
`[0,1]`. -/
def rationalClippedAffine₂ (constant first second : ℚ) : Connective 2 where
  toFun := fun values ↦ clampTruthValue
    ((constant : ℝ) + (first : ℝ) * (values 0 : ℝ) +
      (second : ℝ) * (values 1 : ℝ))
  continuous_toFun := by
    have hzero : Continuous fun values : Fin 2 → TruthValue ↦
        (values 0 : ℝ) :=
      continuous_subtype_val.comp (continuous_apply 0)
    have hone : Continuous fun values : Fin 2 → TruthValue ↦
        (values 1 : ℝ) :=
      continuous_subtype_val.comp (continuous_apply 1)
    exact continuous_clampTruthValue.comp
      ((continuous_const.add (continuous_const.mul hzero)).add
        (continuous_const.mul hone))

/-- Binary minimum as a bounded continuous connective. -/
def rationalMinConnective : Connective 2 where
  toFun := fun values ↦ ⟨min (values 0 : ℝ) (values 1 : ℝ),
    le_min (values 0).property.1 (values 1).property.1,
    (min_le_left _ _).trans (values 0).property.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      (continuous_subtype_val.comp (continuous_apply 0)).min
        (continuous_subtype_val.comp (continuous_apply 1))

/-- Binary maximum as a bounded continuous connective. -/
def rationalMaxConnective : Connective 2 where
  toFun := fun values ↦ ⟨max (values 0 : ℝ) (values 1 : ℝ),
    (values 0).property.1.trans (le_max_left _ _),
    max_le (values 0).property.2 (values 1).property.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      (continuous_subtype_val.comp (continuous_apply 0)).max
        (continuous_subtype_val.comp (continuous_apply 1))

end

end NormFormula.ContinuousLogic
