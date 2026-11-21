import NormFormula.ContinuousLogic.BanachBallCountableSyntax
import NormFormula.ContinuousLogic.ConnectiveApproximation

/-!
# Uniform density of rational ball-sorted formulas

The encodable codes from `BanachBallCountableSyntax` are closed under the
rational lattice operations used by the existing Stone--Weierstrass
approximation theorem.  This file proves their interpretations uniformly
dense in the unrestricted typed ball formulas, simultaneously over all ball
structures and assignments.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u w

namespace CountableBallFormula

/-- Determinism of elaboration identifies the formula selected from a code
with any explicitly exhibited elaboration. -/
theorem toBallFormula_eq_of_elaborate
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n}
    (code : CountableBallFormula Symbol symbolRadius context)
    {formula : BallFormula Symbol symbolRadius context}
    (hformula : code.1.elaborate symbolRadius context = some formula) :
    code.toBallFormula = formula := by
  have hselected := elaborate_toBallFormula code
  exact Option.some.inj (hselected.symm.trans hformula)

/-- A typed distance atom in the countable rational fragment. -/
def distance {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n} {radius : ℚ≥0}
    (left right : BallTerm context radius) :
    CountableBallFormula Symbol symbolRadius context :=
  ⟨.distance radius (RawBallTerm.ofBallTerm left)
      (RawBallTerm.ofBallTerm right),
    .distance left right, by
      simp [RationalBallFormulaCode.elaborate,
        RawBallTerm.elaborateAt_ofBallTerm]⟩

@[simp]
theorem toBallFormula_distance
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n} {radius : ℚ≥0}
    (left right : BallTerm context radius) :
    (distance (Symbol := Symbol) (symbolRadius := symbolRadius)
      left right).toBallFormula = .distance left right :=
  toBallFormula_eq_of_elaborate _ (by
    simp [distance, RationalBallFormulaCode.elaborate,
      RawBallTerm.elaborateAt_ofBallTerm])

/-- A typed named-predicate atom in the countable rational fragment. -/
def predicate {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n} (symbol : Symbol)
    (term : BallTerm context (symbolRadius symbol)) :
    CountableBallFormula Symbol symbolRadius context :=
  ⟨.predicate symbol (RawBallTerm.ofBallTerm term),
    .predicate symbol term, by
      simp [RationalBallFormulaCode.elaborate,
        RawBallTerm.elaborateAt_ofBallTerm]⟩

@[simp]
theorem toBallFormula_predicate
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n} (symbol : Symbol)
    (term : BallTerm context (symbolRadius symbol)) :
    (predicate symbol term).toBallFormula = .predicate symbol term :=
  toBallFormula_eq_of_elaborate _ (by
    simp [predicate, RationalBallFormulaCode.elaborate,
      RawBallTerm.elaborateAt_ofBallTerm])

/-- A rational truth constant in the countable typed fragment. -/
def constant {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n} (value : ℚ) :
    CountableBallFormula Symbol symbolRadius context :=
  ⟨.constant value, .constant (clampTruthValue value), rfl⟩

@[simp]
theorem toBallFormula_constant
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n} (value : ℚ) :
    (constant (Symbol := Symbol) (symbolRadius := symbolRadius)
      (context := context) value).toBallFormula =
        .constant (clampTruthValue value) :=
  toBallFormula_eq_of_elaborate _ rfl

/-- A rational clipped-affine binary gate in the countable typed fragment. -/
def affine₂ {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n} (bias first second : ℚ)
    (left right : CountableBallFormula Symbol symbolRadius context) :
    CountableBallFormula Symbol symbolRadius context :=
  ⟨.affine₂ bias first second left.1 right.1,
    .connective (rationalClippedAffine₂ bias first second)
      ![left.toBallFormula, right.toBallFormula], by
        simp [RationalBallFormulaCode.elaborate,
          elaborate_toBallFormula left, elaborate_toBallFormula right]⟩

@[simp]
theorem toBallFormula_affine₂
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n} (bias first second : ℚ)
    (left right : CountableBallFormula Symbol symbolRadius context) :
    (affine₂ bias first second left right).toBallFormula =
      .connective (rationalClippedAffine₂ bias first second)
        ![left.toBallFormula, right.toBallFormula] :=
  toBallFormula_eq_of_elaborate _ (by
    simp [affine₂, RationalBallFormulaCode.elaborate,
      elaborate_toBallFormula left, elaborate_toBallFormula right])

/-- Binary minimum in the countable typed fragment. -/
def min {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n}
    (left right : CountableBallFormula Symbol symbolRadius context) :
    CountableBallFormula Symbol symbolRadius context :=
  ⟨.min left.1 right.1,
    .connective rationalMinConnective
      ![left.toBallFormula, right.toBallFormula], by
        simp [RationalBallFormulaCode.elaborate,
          elaborate_toBallFormula left, elaborate_toBallFormula right]⟩

@[simp]
theorem toBallFormula_min
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n}
    (left right : CountableBallFormula Symbol symbolRadius context) :
    (min left right).toBallFormula =
      .connective rationalMinConnective
        ![left.toBallFormula, right.toBallFormula] :=
  toBallFormula_eq_of_elaborate _ (by
    simp [min, RationalBallFormulaCode.elaborate,
      elaborate_toBallFormula left, elaborate_toBallFormula right])

/-- Binary maximum in the countable typed fragment. -/
def max {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n}
    (left right : CountableBallFormula Symbol symbolRadius context) :
    CountableBallFormula Symbol symbolRadius context :=
  ⟨.max left.1 right.1,
    .connective rationalMaxConnective
      ![left.toBallFormula, right.toBallFormula], by
        simp [RationalBallFormulaCode.elaborate,
          elaborate_toBallFormula left, elaborate_toBallFormula right]⟩

@[simp]
theorem toBallFormula_max
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n}
    (left right : CountableBallFormula Symbol symbolRadius context) :
    (max left right).toBallFormula =
      .connective rationalMaxConnective
        ![left.toBallFormula, right.toBallFormula] :=
  toBallFormula_eq_of_elaborate _ (by
    simp [max, RationalBallFormulaCode.elaborate,
      elaborate_toBallFormula left, elaborate_toBallFormula right])

/-- Supremum over a specified rational ball in the countable fragment. -/
def iSup {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n} (radius : ℚ≥0)
    (formula : CountableBallFormula Symbol symbolRadius
      (Fin.cons radius context)) :
    CountableBallFormula Symbol symbolRadius context :=
  ⟨.iSup radius formula.1, .iSup radius formula.toBallFormula, by
    simp [RationalBallFormulaCode.elaborate,
      elaborate_toBallFormula formula]⟩

@[simp]
theorem toBallFormula_iSup
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n} (radius : ℚ≥0)
    (formula : CountableBallFormula Symbol symbolRadius
      (Fin.cons radius context)) :
    (iSup radius formula).toBallFormula =
      .iSup radius formula.toBallFormula :=
  toBallFormula_eq_of_elaborate _ (by
    simp [iSup, RationalBallFormulaCode.elaborate,
      elaborate_toBallFormula formula])

/-- Infimum over a specified rational ball in the countable fragment. -/
def iInf {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n} (radius : ℚ≥0)
    (formula : CountableBallFormula Symbol symbolRadius
      (Fin.cons radius context)) :
    CountableBallFormula Symbol symbolRadius context :=
  ⟨.iInf radius formula.1, .iInf radius formula.toBallFormula, by
    simp [RationalBallFormulaCode.elaborate,
      elaborate_toBallFormula formula]⟩

@[simp]
theorem toBallFormula_iInf
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n} (radius : ℚ≥0)
    (formula : CountableBallFormula Symbol symbolRadius
      (Fin.cons radius context)) :
    (iInf radius formula).toBallFormula =
      .iInf radius formula.toBallFormula :=
  toBallFormula_eq_of_elaborate _ (by
    simp [iInf, RationalBallFormulaCode.elaborate,
      elaborate_toBallFormula formula])

end CountableBallFormula

namespace RationalLatticeCode

/-- Substitute countable typed formulas for the coordinates of a rational
lattice code. -/
def instantiateBallFormula
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n arity : ℕ} {context : BallContext n}
    (code : RationalLatticeCode arity)
    (inputs : Fin arity → CountableBallFormula Symbol symbolRadius context) :
    CountableBallFormula Symbol symbolRadius context :=
  match code with
  | .constant value => CountableBallFormula.constant value
  | .affine coordinate bias slope =>
      CountableBallFormula.affine₂ bias slope 0
        (inputs coordinate) (CountableBallFormula.constant 0)
  | .min left right =>
      CountableBallFormula.min
        (left.instantiateBallFormula inputs)
        (right.instantiateBallFormula inputs)
  | .max left right =>
      CountableBallFormula.max
        (left.instantiateBallFormula inputs)
        (right.instantiateBallFormula inputs)

/-- Evaluation of typed lattice substitution is its recursively bounded
interpretation on the input evaluations. -/
theorem realize_instantiateBallFormula_eq_recursiveBoundedValue
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n arity : ℕ} {context : BallContext n}
    (code : RationalLatticeCode arity)
    (inputs : Fin arity → CountableBallFormula Symbol symbolRadius context)
    (M : BallStructure.{u, w} Symbol symbolRadius)
    (assignment : BallTerm.Assignment M.toRationalBallSystem context) :
    (code.instantiateBallFormula inputs).toBallFormula.realize M assignment =
      code.recursiveBoundedValue (fun coordinate =>
        (inputs coordinate).toBallFormula.realize M assignment) := by
  induction code with
  | constant value =>
      simp [instantiateBallFormula, recursiveBoundedValue]
  | affine coordinate bias slope =>
      simp [instantiateBallFormula, recursiveBoundedValue,
        rationalClippedAffine₂, clampTruthValue]
  | min left right leftInduction rightInduction =>
      apply Subtype.ext
      simp [instantiateBallFormula, recursiveBoundedValue,
        rationalMinConnective, leftInduction, rightInduction]
  | max left right leftInduction rightInduction =>
      apply Subtype.ext
      simp [instantiateBallFormula, recursiveBoundedValue,
        rationalMaxConnective, leftInduction, rightInduction]

/-- Evaluation of typed lattice substitution is application of the bounded
connective denoted by the code. -/
theorem realize_instantiateBallFormula_eq_toConnective
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n arity : ℕ} {context : BallContext n}
    (code : RationalLatticeCode arity)
    (inputs : Fin arity → CountableBallFormula Symbol symbolRadius context)
    (M : BallStructure.{u, w} Symbol symbolRadius)
    (assignment : BallTerm.Assignment M.toRationalBallSystem context) :
    (code.instantiateBallFormula inputs).toBallFormula.realize M assignment =
      code.toConnective (fun coordinate =>
        (inputs coordinate).toBallFormula.realize M assignment) := by
  rw [realize_instantiateBallFormula_eq_recursiveBoundedValue]
  exact code.recursiveBoundedValue_eq_boundedValue _

end RationalLatticeCode

namespace BallFormula

/-- Ball-sort supremum quantification does not enlarge a uniform semantic
error. -/
theorem abs_realize_iSup_sub_iSup_le
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n} (radius : ℚ≥0)
    (first second : BallFormula Symbol symbolRadius (Fin.cons radius context))
    (M : BallStructure.{u, w} Symbol symbolRadius)
    (assignment : BallTerm.Assignment M.toRationalBallSystem context)
    {ε : ℝ}
    (h : ∀ x : M.Ball radius,
      |(first.realize M (Fin.cons x assignment) : ℝ) -
        (second.realize M (Fin.cons x assignment) : ℝ)| ≤ ε) :
    |((BallFormula.iSup radius first).realize M assignment : ℝ) -
      ((BallFormula.iSup radius second).realize M assignment : ℝ)| ≤ ε :=
  abs_coe_iSup_sub_coe_iSup_le _ _ h

/-- Ball-sort infimum quantification does not enlarge a uniform semantic
error. -/
theorem abs_realize_iInf_sub_iInf_le
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n} (radius : ℚ≥0)
    (first second : BallFormula Symbol symbolRadius (Fin.cons radius context))
    (M : BallStructure.{u, w} Symbol symbolRadius)
    (assignment : BallTerm.Assignment M.toRationalBallSystem context)
    {ε : ℝ}
    (h : ∀ x : M.Ball radius,
      |(first.realize M (Fin.cons x assignment) : ℝ) -
        (second.realize M (Fin.cons x assignment) : ℝ)| ≤ ε) :
    |((BallFormula.iInf radius first).realize M assignment : ℝ) -
      ((BallFormula.iInf radius second).realize M assignment : ℝ)| ≤ ε :=
  abs_coe_iInf_sub_coe_iInf_le _ _ h

/-- Every unrestricted typed ball formula is uniformly approximated by one
well-typed formula in the countable rational fragment, simultaneously in
every ball structure and under every assignment. -/
theorem exists_countableBallFormula_uniformly_close
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n}
    (formula : BallFormula Symbol symbolRadius context)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ rational : CountableBallFormula Symbol symbolRadius context,
      ∀ (M : BallStructure.{u, w} Symbol symbolRadius)
        (assignment : BallTerm.Assignment M.toRationalBallSystem context),
        |(rational.toBallFormula.realize M assignment : ℝ) -
          (formula.realize M assignment : ℝ)| < ε := by
  induction formula generalizing ε with
  | distance left right =>
      refine ⟨CountableBallFormula.distance left right, ?_⟩
      intro M assignment
      simp only [CountableBallFormula.toBallFormula_distance]
      simpa using hε
  | predicate symbol term =>
      refine ⟨CountableBallFormula.predicate symbol term, ?_⟩
      intro M assignment
      simp only [CountableBallFormula.toBallFormula_predicate]
      simpa using hε
  | constant value =>
      have hinterval : (value : ℝ) - ε < (value : ℝ) + ε := by
        linarith
      obtain ⟨rational, hlower, hupper⟩ := exists_rat_btwn hinterval
      refine ⟨CountableBallFormula.constant rational, ?_⟩
      intro M assignment
      have hvalue : clampTruthValue (value : ℝ) = value := by
        apply Subtype.ext
        simp [clampTruthValue, value.property.1, value.property.2]
      simp only [CountableBallFormula.toBallFormula_constant,
        BallFormula.realize_constant]
      change |(clampTruthValue (rational : ℝ) : ℝ) - (value : ℝ)| < ε
      rw [← hvalue]
      exact (abs_clampTruthValue_sub_clampTruthValue_le
        (rational : ℝ) value).trans_lt (by
          rw [abs_lt]
          constructor <;> linarith)
  | connective connective formulas induction =>
      obtain ⟨δ, hδ, hmodulus⟩ :=
        connective.exists_coordinatewise_tolerance (half_pos hε)
      choose inputs hclose using fun coordinate => induction coordinate hδ
      obtain ⟨code, hcode⟩ :=
        connective.exists_rationalLatticeCode_uniformly_close (half_pos hε)
      refine ⟨code.instantiateBallFormula inputs, ?_⟩
      intro M assignment
      rw [code.realize_instantiateBallFormula_eq_toConnective]
      have hchildren :
          |(connective (fun coordinate =>
              (inputs coordinate).toBallFormula.realize M assignment) : ℝ) -
            (connective (fun coordinate =>
              (formulas coordinate).realize M assignment) : ℝ)| < ε / 2 :=
        hmodulus _ _ fun coordinate => hclose coordinate M assignment
      calc
        |(code.toConnective (fun coordinate =>
              (inputs coordinate).toBallFormula.realize M assignment) : ℝ) -
            (connective (fun coordinate =>
              (formulas coordinate).realize M assignment) : ℝ)| ≤
          |(code.toConnective (fun coordinate =>
                (inputs coordinate).toBallFormula.realize M assignment) : ℝ) -
              (connective (fun coordinate =>
                (inputs coordinate).toBallFormula.realize M assignment) : ℝ)| +
            |(connective (fun coordinate =>
                (inputs coordinate).toBallFormula.realize M assignment) : ℝ) -
              (connective (fun coordinate =>
                (formulas coordinate).realize M assignment) : ℝ)| :=
          abs_sub_le _ _ _
        _ < ε := by
          have hcode' := hcode (fun coordinate =>
            (inputs coordinate).toBallFormula.realize M assignment)
          linarith
  | iSup radius formula induction =>
      obtain ⟨rational, hclose⟩ := induction (half_pos hε)
      refine ⟨CountableBallFormula.iSup radius rational, ?_⟩
      intro M assignment
      simp only [CountableBallFormula.toBallFormula_iSup]
      have hbound := abs_realize_iSup_sub_iSup_le radius
        rational.toBallFormula formula M assignment
        (fun x => (hclose M (Fin.cons x assignment)).le)
      exact hbound.trans_lt (half_lt_self hε)
  | iInf radius formula induction =>
      obtain ⟨rational, hclose⟩ := induction (half_pos hε)
      refine ⟨CountableBallFormula.iInf radius rational, ?_⟩
      intro M assignment
      simp only [CountableBallFormula.toBallFormula_iInf]
      have hbound := abs_realize_iInf_sub_iInf_le radius
        rational.toBallFormula formula M assignment
        (fun x => (hclose M (Fin.cons x assignment)).le)
      exact hbound.trans_lt (half_lt_self hε)

end BallFormula

end

end NormFormula.ContinuousLogic
