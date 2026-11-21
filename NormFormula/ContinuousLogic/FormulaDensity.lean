import NormFormula.ContinuousLogic.ConnectiveApproximation

/-!
# Uniform density of the rational formula fragment

Every formula with arbitrary bounded continuous connectives is uniformly
approximated by a well-formed formula in the countable rational fragment.
The approximation is simultaneous over all structures and assignments.

The proof is structural.  Rational constants approximate arbitrary truth
constants, compactness supplies a common input tolerance at connective nodes,
rational lattice codes approximate the resulting connective on rational
children, and supremum and infimum quantifiers preserve uniform error.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

namespace MultiFormula

/-- Every unrestricted continuous formula admits a uniformly close
well-formed formula in the rational fragment, simultaneously in every
many-predicate structure and under every assignment. -/
theorem exists_rationalFormula_uniformly_close
    {Symbol : Type*} {rowVars parameterVars : ℕ}
    (formula : MultiFormula Symbol rowVars parameterVars)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ rational : RationalFormula Symbol,
      ∃ hrational : rational.WellFormed rowVars parameterVars,
        ∀ (M : MultiStructure Symbol)
          (rows : Fin rowVars → M.Row)
          (parameters : Fin parameterVars → M.Parameter),
          |((rational.toMultiFormula rowVars parameterVars hrational).realize
              M rows parameters : ℝ) -
            (formula.realize M rows parameters : ℝ)| < ε := by
  induction formula generalizing ε with
  | predicate symbol row parameter =>
      refine ⟨.predicate symbol row parameter, ⟨row.isLt, parameter.isLt⟩, ?_⟩
      intro M rows parameters
      simpa [RationalFormula.toMultiFormula, MultiFormula.realize] using hε
  | constant value =>
      have hinterval : (value : ℝ) - ε < (value : ℝ) + ε := by
        linarith
      obtain ⟨rational, hlower, hupper⟩ := exists_rat_btwn hinterval
      refine ⟨.constant rational, trivial, ?_⟩
      intro M rows parameters
      have hvalue : clampTruthValue (value : ℝ) = value := by
        apply Subtype.ext
        simp [clampTruthValue, value.property.1, value.property.2]
      change |(clampTruthValue (rational : ℝ) : ℝ) - (value : ℝ)| < ε
      rw [← hvalue]
      exact (abs_clampTruthValue_sub_clampTruthValue_le
        (rational : ℝ) value).trans_lt (by
          rw [abs_lt]
          constructor <;> linarith)
  | connective connective formulas induction =>
      obtain ⟨δ, hδ, hmodulus⟩ :=
        connective.exists_coordinatewise_tolerance (half_pos hε)
      choose inputs hinputs hclose using fun coordinate => induction coordinate hδ
      obtain ⟨rational, hrational, hcode⟩ :=
        connective.exists_rationalFormula_uniformly_close_of_inputs
          inputs hinputs (half_pos hε)
      refine ⟨rational, hrational, ?_⟩
      intro M rows parameters
      have hchildren :
          |(connective (fun coordinate =>
              ((inputs coordinate).toMultiFormula _ _
                (hinputs coordinate)).realize M rows parameters) : ℝ) -
            (connective (fun coordinate =>
              (formulas coordinate).realize M rows parameters) : ℝ)| < ε / 2 :=
        hmodulus _ _ fun coordinate => hclose coordinate M rows parameters
      calc
        |((rational.toMultiFormula _ _ hrational).realize
              M rows parameters : ℝ) -
            (connective (fun coordinate =>
              (formulas coordinate).realize M rows parameters) : ℝ)|
            ≤ |((rational.toMultiFormula _ _ hrational).realize
                  M rows parameters : ℝ) -
                (connective (fun coordinate =>
                  ((inputs coordinate).toMultiFormula _ _
                    (hinputs coordinate)).realize M rows parameters) : ℝ)| +
              |(connective (fun coordinate =>
                  ((inputs coordinate).toMultiFormula _ _
                    (hinputs coordinate)).realize M rows parameters) : ℝ) -
                (connective (fun coordinate =>
                  (formulas coordinate).realize M rows parameters) : ℝ)| :=
              abs_sub_le _ _ _
        _ < ε := by
          have hcode' := hcode M rows parameters
          linarith
  | iSupRow formula induction =>
      obtain ⟨rational, hrational, hclose⟩ := induction (half_pos hε)
      refine ⟨.iSupRow rational, hrational, ?_⟩
      intro M rows parameters
      have hbound := abs_realize_iSupRow_sub_iSupRow_le
        (rational.toMultiFormula _ _ hrational)
        formula M rows parameters
        (fun x => (hclose M (Fin.cons x rows) parameters).le)
      exact hbound.trans_lt (half_lt_self hε)
  | iInfRow formula induction =>
      obtain ⟨rational, hrational, hclose⟩ := induction (half_pos hε)
      refine ⟨.iInfRow rational, hrational, ?_⟩
      intro M rows parameters
      have hbound := abs_realize_iInfRow_sub_iInfRow_le
        (rational.toMultiFormula _ _ hrational)
        formula M rows parameters
        (fun x => (hclose M (Fin.cons x rows) parameters).le)
      exact hbound.trans_lt (half_lt_self hε)
  | iSupParameter formula induction =>
      obtain ⟨rational, hrational, hclose⟩ := induction (half_pos hε)
      refine ⟨.iSupParameter rational, hrational, ?_⟩
      intro M rows parameters
      have hbound := abs_realize_iSupParameter_sub_iSupParameter_le
        (rational.toMultiFormula _ _ hrational)
        formula M rows parameters
        (fun y => (hclose M rows (Fin.cons y parameters)).le)
      exact hbound.trans_lt (half_lt_self hε)
  | iInfParameter formula induction =>
      obtain ⟨rational, hrational, hclose⟩ := induction (half_pos hε)
      refine ⟨.iInfParameter rational, hrational, ?_⟩
      intro M rows parameters
      have hbound := abs_realize_iInfParameter_sub_iInfParameter_le
        (rational.toMultiFormula _ _ hrational)
        formula M rows parameters
        (fun y => (hclose M rows (Fin.cons y parameters)).le)
      exact hbound.trans_lt (half_lt_self hε)

end MultiFormula

end

end NormFormula.ContinuousLogic
