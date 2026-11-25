import Mathlib.Tactic.DeriveEncodable
import NormFormula.ContinuousLogic.BanachBallFormula
import NormFormula.ContinuousLogic.CountableSyntax

/-!
# Countable codes for the rational-ball language

The intrinsic `BallTerm` and `BallFormula` types enforce all radius equations
in their indices, but proof-valued inclusion data make them inconvenient to
enumerate directly.  This file introduces raw, explicitly encodable codes and
partial elaborators into the intrinsic syntax.

The formula codes use the same rational constants, clipped affine binary
gates, minimum, and maximum as the existing countable continuous fragment.
They also record the quantified rational ball at every binder.  Consequently,
for an encodable predicate alphabet and any fixed finite ball context, the
well-typed rational formula codes form a countable family of genuine typed
ball formulas.  A later density theorem can therefore feed these codes to a
many-sorted witness construction.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe w

/-- Raw codes for radius-indexed Banach terms.  Radius correctness is checked
by `RawBallTerm.elaborate`. -/
inductive RawBallTerm where
  | variable (index : ℕ)
  | inclusion (target : ℚ≥0) (term : RawBallTerm)
  | zero (radius : ℚ≥0)
  | neg (term : RawBallTerm)
  | add (left right : RawBallTerm)
  | smul (scalar : ℚ) (term : RawBallTerm)
  deriving Encodable

namespace RawBallTerm

/-- Partially elaborate a raw term, returning its inferred output radius and
an intrinsically typed term. -/
def elaborate {n : ℕ} (context : BallContext n) :
    RawBallTerm → Option (Σ radius, BallTerm context radius)
  | .variable index =>
      if hindex : index < n then
        let i : Fin n := ⟨index, hindex⟩
        some ⟨context i, .variable i⟩
      else none
  | .inclusion target term =>
      match term.elaborate context with
      | none => none
      | some ⟨source, typed⟩ =>
          if hradius : source ≤ target then
            some ⟨target, .inclusion hradius typed⟩
          else none
  | .zero radius => some ⟨radius, .zero radius⟩
  | .neg term =>
      match term.elaborate context with
      | none => none
      | some ⟨radius, typed⟩ => some ⟨radius, .neg typed⟩
  | .add left right =>
      match left.elaborate context, right.elaborate context with
      | some ⟨leftRadius, leftTyped⟩, some ⟨rightRadius, rightTyped⟩ =>
          some ⟨leftRadius + rightRadius, .add leftTyped rightTyped⟩
      | _, _ => none
  | .smul scalar term =>
      match term.elaborate context with
      | none => none
      | some ⟨radius, typed⟩ =>
          some ⟨scalar.nnabs * radius, .smul scalar typed⟩

/-- Elaborate a raw term at a prescribed output radius. -/
def elaborateAt {n : ℕ} (context : BallContext n) (radius : ℚ≥0)
    (code : RawBallTerm) : Option (BallTerm context radius) :=
  match code.elaborate context with
  | none => none
  | some ⟨inferred, term⟩ =>
      if hradius : inferred = radius then
        some (hradius ▸ term)
      else none

/-- Erase the dependent radius indices of a typed term. -/
def ofBallTerm {n : ℕ} {context : BallContext n} {radius : ℚ≥0} :
    BallTerm context radius → RawBallTerm
  | .variable i => .variable i
  | .inclusion (s := target) _ term => .inclusion target (ofBallTerm term)
  | .zero r => .zero r
  | .neg term => .neg (ofBallTerm term)
  | .add left right => .add (ofBallTerm left) (ofBallTerm right)
  | .smul scalar term => .smul scalar (ofBallTerm term)

/-- Erasing and re-elaborating a typed term recovers its output radius and
the original intrinsic term. -/
theorem elaborate_ofBallTerm
    {n : ℕ} {context : BallContext n} {radius : ℚ≥0}
    (term : BallTerm context radius) :
    (ofBallTerm term).elaborate context = some ⟨radius, term⟩ := by
  induction term with
  | «variable» i =>
      simp [ofBallTerm, elaborate, i.isLt]
  | inclusion h term induction =>
      simp [ofBallTerm, elaborate, induction, h]
  | zero r =>
      rfl
  | neg term induction =>
      simp [ofBallTerm, elaborate, induction]
  | add left right leftInduction rightInduction =>
      simp [ofBallTerm, elaborate, leftInduction, rightInduction]
  | smul scalar term induction =>
      simp [ofBallTerm, elaborate, induction]

/-- Erasing and re-elaborating at the known radius recovers a typed term. -/
theorem elaborateAt_ofBallTerm
    {n : ℕ} {context : BallContext n} {radius : ℚ≥0}
    (term : BallTerm context radius) :
    (ofBallTerm term).elaborateAt context radius = some term := by
  simp [elaborateAt, elaborate_ofBallTerm]

end RawBallTerm

/-- Raw rational formula codes for the ball-sorted language. -/
inductive RationalBallFormulaCode (Symbol : Type w) where
  | distance (radius : ℚ≥0) (left right : RawBallTerm)
  | predicate (symbol : Symbol) (term : RawBallTerm)
  | constant (value : ℚ)
  | affine₂ (bias first second : ℚ)
      (left right : RationalBallFormulaCode Symbol)
  | min (left right : RationalBallFormulaCode Symbol)
  | max (left right : RationalBallFormulaCode Symbol)
  | iSup (radius : ℚ≥0) (formula : RationalBallFormulaCode Symbol)
  | iInf (radius : ℚ≥0) (formula : RationalBallFormulaCode Symbol)
  deriving Encodable

namespace RationalBallFormulaCode

/-- Partially elaborate a rational formula code in a fixed typed context. -/
def elaborate {Symbol : Type w} (symbolRadius : Symbol → ℚ≥0) :
    {n : ℕ} → (context : BallContext n) →
      RationalBallFormulaCode Symbol →
        Option (BallFormula Symbol symbolRadius context)
  | _, context, .distance radius left right =>
      match left.elaborateAt context radius,
          right.elaborateAt context radius with
      | some leftTyped, some rightTyped =>
          some (.distance leftTyped rightTyped)
      | _, _ => none
  | _, context, .predicate symbol term =>
      match term.elaborateAt context (symbolRadius symbol) with
      | some typed => some (.predicate symbol typed)
      | none => none
  | _, _, .constant value =>
      some (.constant (clampTruthValue value))
  | _, context, .affine₂ bias first second left right =>
      match left.elaborate symbolRadius context,
          right.elaborate symbolRadius context with
      | some leftTyped, some rightTyped =>
          some (.connective (rationalClippedAffine₂ bias first second)
            ![leftTyped, rightTyped])
      | _, _ => none
  | _, context, .min left right =>
      match left.elaborate symbolRadius context,
          right.elaborate symbolRadius context with
      | some leftTyped, some rightTyped =>
          some (.connective rationalMinConnective ![leftTyped, rightTyped])
      | _, _ => none
  | _, context, .max left right =>
      match left.elaborate symbolRadius context,
          right.elaborate symbolRadius context with
      | some leftTyped, some rightTyped =>
          some (.connective rationalMaxConnective ![leftTyped, rightTyped])
      | _, _ => none
  | _, context, .iSup radius formula =>
      match formula.elaborate symbolRadius (Fin.cons radius context) with
      | some typed => some (.iSup radius typed)
      | none => none
  | _, context, .iInf radius formula =>
      match formula.elaborate symbolRadius (Fin.cons radius context) with
      | some typed => some (.iInf radius typed)
      | none => none

end RationalBallFormulaCode

/-- Well-typed rational formula codes in one fixed ball context. -/
def CountableBallFormula (Symbol : Type w) (symbolRadius : Symbol → ℚ≥0)
    {n : ℕ} (context : BallContext n) :=
  {code : RationalBallFormulaCode Symbol //
    ∃ formula : BallFormula Symbol symbolRadius context,
      code.elaborate symbolRadius context = some formula}

noncomputable instance {Symbol : Type w} [Encodable Symbol]
    (symbolRadius : Symbol → ℚ≥0) {n : ℕ} (context : BallContext n) :
    Countable (CountableBallFormula Symbol symbolRadius context) :=
  Function.Injective.countable Subtype.val_injective

namespace CountableBallFormula

/-- The genuine typed formula denoted by a well-typed rational code. -/
def toBallFormula {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n}
    (code : CountableBallFormula Symbol symbolRadius context) :
    BallFormula Symbol symbolRadius context :=
  Classical.choose code.2

/-- The selected formula is the elaboration of its raw rational code. -/
theorem elaborate_toBallFormula
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n}
    (code : CountableBallFormula Symbol symbolRadius context) :
    code.1.elaborate symbolRadius context = some code.toBallFormula :=
  Classical.choose_spec code.2


end CountableBallFormula

end

end NormFormula.ContinuousLogic
