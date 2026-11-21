import Mathlib.Logic.Encodable.Pi
import Mathlib.Tactic.DeriveEncodable
import NormFormula.ContinuousLogic.MultiPredicate

/-!
# A countable rational fragment of continuous syntax

The unrestricted formula syntax permits arbitrary truth constants and
arbitrary continuous connectives, so it is not countable even for a finite
predicate alphabet.  Downward Löwenheim--Skolem instead works with a
countable dense fragment.  This file defines such a fragment using rational
constants, rational clipped-affine binary gates, finite minimum and maximum,
and the four quantifiers, and embeds it into `MultiFormula`.

`RationalConnectiveDensity` proves density of the interpreted rational
piecewise-affine connectives in all continuous connectives on finite
truth-value cubes.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open scoped Topology

universe w

/-- Clamp a real number to the truth-value interval `[0,1]`. -/
def clampTruthValue (x : ℝ) : TruthValue :=
  ⟨max 0 (min 1 x),
    le_max_left _ _,
    max_le zero_le_one (min_le_left _ _)⟩

@[simp]
theorem clampTruthValue_coe (x : ℝ) :
    (clampTruthValue x : ℝ) = max 0 (min 1 x) :=
  rfl

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

/-- Raw countable formula codes. Natural variable indices are checked by the
separate `WellFormed` predicate below. Direct recursive binary gates keep this
datatype explicitly encodable. -/
inductive RationalFormula (Symbol : Type w) where
  | predicate : Symbol → ℕ → ℕ → RationalFormula Symbol
  | constant : ℚ → RationalFormula Symbol
  | affine₂ : ℚ → ℚ → ℚ → RationalFormula Symbol →
      RationalFormula Symbol → RationalFormula Symbol
  | min : RationalFormula Symbol → RationalFormula Symbol →
      RationalFormula Symbol
  | max : RationalFormula Symbol → RationalFormula Symbol →
      RationalFormula Symbol
  | iSupRow : RationalFormula Symbol → RationalFormula Symbol
  | iInfRow : RationalFormula Symbol → RationalFormula Symbol
  | iSupParameter : RationalFormula Symbol → RationalFormula Symbol
  | iInfParameter : RationalFormula Symbol → RationalFormula Symbol
  deriving Encodable

namespace RationalFormula

/-- A raw rational formula is well formed for the indicated numbers of free
row and parameter variables. -/
def WellFormed {Symbol : Type w} :
    ℕ → ℕ → RationalFormula Symbol → Prop
  | rowVars, parameterVars, .predicate _ row parameter =>
      row < rowVars ∧ parameter < parameterVars
  | _, _, .constant _ => True
  | rowVars, parameterVars, .affine₂ _ _ _ first second =>
      first.WellFormed rowVars parameterVars ∧
        second.WellFormed rowVars parameterVars
  | rowVars, parameterVars, .min first second =>
      first.WellFormed rowVars parameterVars ∧
        second.WellFormed rowVars parameterVars
  | rowVars, parameterVars, .max first second =>
      first.WellFormed rowVars parameterVars ∧
        second.WellFormed rowVars parameterVars
  | rowVars, parameterVars, .iSupRow formula =>
      formula.WellFormed (rowVars + 1) parameterVars
  | rowVars, parameterVars, .iInfRow formula =>
      formula.WellFormed (rowVars + 1) parameterVars
  | rowVars, parameterVars, .iSupParameter formula =>
      formula.WellFormed rowVars (parameterVars + 1)
  | rowVars, parameterVars, .iInfParameter formula =>
      formula.WellFormed rowVars (parameterVars + 1)

/-- Translate a well-formed rational code into the unrestricted continuous
formula syntax. -/
def toMultiFormula {Symbol : Type w} :
    ∀ (formula : RationalFormula Symbol) (rowVars parameterVars : ℕ),
      formula.WellFormed rowVars parameterVars →
        MultiFormula Symbol rowVars parameterVars
  | .predicate symbol row parameter, _, _, h =>
      .predicate symbol ⟨row, h.1⟩ ⟨parameter, h.2⟩
  | .constant value, _, _, _ =>
      .constant (clampTruthValue value)
  | .affine₂ bias firstCoefficient secondCoefficient left right,
      rowVars, parameterVars, h =>
      .connective
        (rationalClippedAffine₂ bias firstCoefficient secondCoefficient)
        (Fin.cases
          (left.toMultiFormula rowVars parameterVars h.1)
          (Fin.cases
            (right.toMultiFormula rowVars parameterVars h.2)
            Fin.elim0))
  | .min left right, rowVars, parameterVars, h =>
      .connective rationalMinConnective
        (Fin.cases
          (left.toMultiFormula rowVars parameterVars h.1)
          (Fin.cases
            (right.toMultiFormula rowVars parameterVars h.2)
            Fin.elim0))
  | .max left right, rowVars, parameterVars, h =>
      .connective rationalMaxConnective
        (Fin.cases
          (left.toMultiFormula rowVars parameterVars h.1)
          (Fin.cases
            (right.toMultiFormula rowVars parameterVars h.2)
            Fin.elim0))
  | .iSupRow formula, rowVars, parameterVars, h =>
      .iSupRow (formula.toMultiFormula (rowVars + 1) parameterVars h)
  | .iInfRow formula, rowVars, parameterVars, h =>
      .iInfRow (formula.toMultiFormula (rowVars + 1) parameterVars h)
  | .iSupParameter formula, rowVars, parameterVars, h =>
      .iSupParameter
        (formula.toMultiFormula rowVars (parameterVars + 1) h)
  | .iInfParameter formula, rowVars, parameterVars, h =>
      .iInfParameter
        (formula.toMultiFormula rowVars (parameterVars + 1) h)

end RationalFormula

/-- Well-formed rational formula codes with fixed free-variable counts. -/
def CountableFormula (Symbol : Type w) (rowVars parameterVars : ℕ) :=
  {formula : RationalFormula Symbol //
    formula.WellFormed rowVars parameterVars}

noncomputable instance {Symbol : Type w} [Encodable Symbol]
    (rowVars parameterVars : ℕ) :
    Countable (CountableFormula Symbol rowVars parameterVars) :=
  Function.Injective.countable Subtype.val_injective

namespace CountableFormula

/-- Embed the countable rational fragment into `MultiFormula`. -/
def toMultiFormula {Symbol : Type w} {rowVars parameterVars : ℕ}
    (formula : CountableFormula Symbol rowVars parameterVars) :
    MultiFormula Symbol rowVars parameterVars :=
  formula.1.toMultiFormula rowVars parameterVars formula.2

/-- The image of the rational fragment is a countable family of unrestricted
formulae. -/
theorem range_toMultiFormula_countable
    {Symbol : Type w} [Encodable Symbol]
    (rowVars parameterVars : ℕ) :
    (Set.range (toMultiFormula :
      CountableFormula Symbol rowVars parameterVars →
        MultiFormula Symbol rowVars parameterVars)).Countable :=
  Set.countable_range _

/-- The atomic formula for a chosen predicate symbol belongs to the
countable fragment. -/
def atomic {Symbol : Type w} (symbol : Symbol) :
    CountableFormula Symbol 1 1 :=
  ⟨.predicate symbol 0 0, by simp [RationalFormula.WellFormed]⟩

@[simp]
theorem atomic_toMultiFormula {Symbol : Type w} (symbol : Symbol) :
    (atomic symbol).toMultiFormula =
      (MultiFormula.predicate symbol 0 0 : MultiFormula Symbol 1 1) :=
  by
    simp [atomic, toMultiFormula, RationalFormula.toMultiFormula]

end CountableFormula

end

end NormFormula.ContinuousLogic
