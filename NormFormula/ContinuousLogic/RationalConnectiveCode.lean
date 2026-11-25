import NormFormula.ContinuousLogic.CountableSyntax

/-!
# Rational lattice codes for continuous connectives

This file isolates the countable connective family used in the
uniform-density theorem. A code is a finite lattice expression built from
rational constants and rational affine functions of one coordinate.  Its
real interpretation is piecewise affine; clamping the final value produces a
bounded continuous connective.

Although the leaves are only one-coordinate affine functions, they separate
points of every finite truth-value cube.  Finite minima and maxima are
therefore the right input for the lattice form of Stone--Weierstrass.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open scoped Topology

/-- A finite rational lattice expression on an `arity`-dimensional
truth-value cube. -/
inductive RationalLatticeCode (arity : ℕ) where
  | constant : ℚ → RationalLatticeCode arity
  | affine : Fin arity → ℚ → ℚ → RationalLatticeCode arity
  | min : RationalLatticeCode arity → RationalLatticeCode arity →
      RationalLatticeCode arity
  | max : RationalLatticeCode arity → RationalLatticeCode arity →
      RationalLatticeCode arity
  deriving Encodable

namespace RationalLatticeCode

/-- The unbounded real-valued piecewise-affine interpretation of a rational
lattice code. -/
def realValue {arity : ℕ} :
    RationalLatticeCode arity → (Fin arity → TruthValue) → ℝ
  | .constant value, _ => value
  | .affine coordinate bias slope, values =>
      (bias : ℝ) + (slope : ℝ) * (values coordinate : ℝ)
  | .min left right, values =>
      Min.min (left.realValue values) (right.realValue values)
  | .max left right, values =>
      Max.max (left.realValue values) (right.realValue values)

/-- Every rational lattice code denotes a continuous real-valued function. -/
theorem continuous_realValue {arity : ℕ}
    (code : RationalLatticeCode arity) : Continuous code.realValue := by
  induction code with
  | constant value => exact continuous_const
  | affine coordinate bias slope =>
      exact continuous_const.add
        (continuous_const.mul
          (continuous_subtype_val.comp (continuous_apply coordinate)))
  | min left right leftContinuous rightContinuous =>
      exact leftContinuous.min rightContinuous
  | max left right leftContinuous rightContinuous =>
      exact leftContinuous.max rightContinuous

/-- The bundled continuous real interpretation of a rational lattice code. -/
def realContinuousMap {arity : ℕ} (code : RationalLatticeCode arity) :
    C((Fin arity → TruthValue), ℝ) :=
  ⟨code.realValue, code.continuous_realValue⟩

/-- The bounded interpretation obtained by clamping only the final
piecewise-affine value. -/
def boundedValue {arity : ℕ} (code : RationalLatticeCode arity)
    (values : Fin arity → TruthValue) : TruthValue :=
  clampTruthValue (code.realValue values)

/-- A rational lattice code determines an unrestricted continuous
connective. -/
def toConnective {arity : ℕ}
    (code : RationalLatticeCode arity) : Connective arity where
  toFun := code.boundedValue
  continuous_toFun :=
    continuous_clampTruthValue.comp code.continuous_realValue

/-- Rational lattice codes are countable in every fixed arity. -/
instance (arity : ℕ) : Countable (RationalLatticeCode arity) :=
  Encodable.countable

end RationalLatticeCode

/-- Clamping is monotone. -/
theorem monotone_clampTruthValue : Monotone clampTruthValue := by
  intro first second h
  change max 0 (min 1 first) ≤ max 0 (min 1 second)
  exact max_le_max_left 0 (min_le_min_left 1 h)

@[simp]
theorem clampTruthValue_min (first second : ℝ) :
    clampTruthValue (min first second) =
      min (clampTruthValue first) (clampTruthValue second) :=
  monotone_clampTruthValue.map_min

@[simp]
theorem clampTruthValue_max (first second : ℝ) :
    clampTruthValue (max first second) =
      max (clampTruthValue first) (clampTruthValue second) :=
  monotone_clampTruthValue.map_max

namespace RationalLatticeCode

/-- The bounded interpretation can be computed by clamping the affine leaves
and then applying the truth-value lattice operations.  This is the algebraic
fact that lets the code be expanded into `RationalFormula`. -/
def recursiveBoundedValue {arity : ℕ} :
    RationalLatticeCode arity → (Fin arity → TruthValue) → TruthValue
  | .constant value, _ => clampTruthValue value
  | .affine coordinate bias slope, values =>
      clampTruthValue ((bias : ℝ) + (slope : ℝ) * (values coordinate : ℝ))
  | .min left right, values =>
      Min.min (left.recursiveBoundedValue values)
        (right.recursiveBoundedValue values)
  | .max left right, values =>
      Max.max (left.recursiveBoundedValue values)
        (right.recursiveBoundedValue values)

/-- Final clamping agrees with recursive clamping at the affine leaves. -/
theorem recursiveBoundedValue_eq_boundedValue {arity : ℕ}
    (code : RationalLatticeCode arity)
    (values : Fin arity → TruthValue) :
    code.recursiveBoundedValue values = code.boundedValue values := by
  induction code with
  | constant value => rfl
  | affine coordinate bias slope => rfl
  | min left right leftInduction rightInduction =>
      simp only [recursiveBoundedValue, boundedValue, realValue,
        clampTruthValue_min, leftInduction, rightInduction]
  | max left right leftInduction rightInduction =>
      simp only [recursiveBoundedValue, boundedValue, realValue,
        clampTruthValue_max, leftInduction, rightInduction]


end RationalLatticeCode

end

end NormFormula.ContinuousLogic
