import NormFormula.ContinuousLogic.FinitePatternTransfer
import NormFormula.ContinuousLogic.YExpansion
import NormFormula.ModelTheory.YNormLocalNIP

/-!
# Finite-pattern NIP for the named predicates on `Y`

The complete-theory finite-pattern transfer theorem converts the concrete
bounded-local-NIP estimates for the Hilbert and `q` translations into genuine
complete-theory NIP statements for their normalized atomic formulae in the
bounded expansion of `Y`.
-/

namespace NormFormula.HalfGraph.Y.ContinuousLanguage

noncomputable section

open NormFormula.ContinuousLogic

/-- A bounded-local-NIP estimate for an unnormalized predicate on `Y` rules
out finite patterns in every dimension for its normalization by `2R` on the
positive `R`-ball. -/
private theorem no_finitePatterns_of_normalized_boundedLocalNIP
    (R : ℝ) (hR : 0 < R)
    (formula : MultiFormula ExpansionSymbol 1 1)
    (value : Y → Y → ℝ)
    (hvalue : ∀ x y : PositiveNormBall Y R,
      formula.binaryValue (expansionStructure R hR) x y =
        value x.1 y.1 / (2 * R))
    (hlocal : NormFormula.IsBoundedLocalNIP value)
    {low high : ℝ} (hgap : low < high) :
    ¬ MultiFormula.HasFiniteIPPatternsInEveryDimension
      (expansionStructure R hR) formula low high := by
  intro hpatterns
  have hdenom : 0 < 2 * R := by positivity
  apply hlocal.not_hasIPPatternsInEveryDimension
    (R_x := R) (R_y := R)
    (low := low * (2 * R)) (high := high * (2 * R))
    (mul_lt_mul_of_pos_right hgap hdenom)
  intro n
  obtain ⟨rows, hip⟩ := hpatterns n
  refine ⟨fun i ↦ (rows i).1, fun i ↦ (rows i).2, ?_⟩
  intro S
  obtain ⟨parameter, hhigh, hlow⟩ := hip S
  refine ⟨parameter, ?_, ?_⟩
  · intro i hi
    have hi := hhigh i hi
    change high ≤ formula.binaryValue
      (expansionStructure R hR) (rows i) parameter at hi
    rw [hvalue] at hi
    change high * (2 * R) ≤ value (rows i).1 parameter.1
    exact (le_div_iff₀ hdenom).mp hi
  · intro i hi
    have hi := hlow i hi
    change formula.binaryValue
      (expansionStructure R hR) (rows i) parameter ≤ low at hi
    rw [hvalue] at hi
    change value (rows i).1 parameter.1 ≤ low * (2 * R)
    exact (div_le_iff₀ hdenom).mp hi

/-- The normalized named Hilbert predicate is NIP in the complete theory of
the bounded `Y`-expansion. -/
theorem hilbertFormula_isNIPInCompleteTheory
    (R : ℝ) (hR : 0 < R) :
    MultiFormula.IsNIPInCompleteTheory
      (expansionStructure R hR) hilbertFormula := by
  apply hilbertPredicate_isNIPInCompleteTheory (expansionStructure R hR) hilbertFormula
    (fun x ↦ x.1.toHilbert) (fun y ↦ y.1.toHilbert) R R (2*R) (by positivity)
    (fun x ↦ (hilbert_norm_le_norm x.1).trans x.2)
    (fun y ↦ (hilbert_norm_le_norm y.1).trans y.2)
  intro x y
  rfl

/-- The normalized named `q` predicate is NIP in the complete theory of the
bounded `Y`-expansion. -/
theorem qFormula_isNIPInCompleteTheory
    (R : ℝ) (hR : 0 < R) :
    MultiFormula.IsNIPInCompleteTheory
      (expansionStructure R hR) qFormula := by
  apply MultiFormula.isNIPInCompleteTheory_of_no_finiteIPPatterns
  intro low high hgap
  apply no_finitePatterns_of_normalized_boundedLocalNIP
    R hR qFormula qPredicateTranslate
  · intro x y
    simp [qPredicateTranslate]
  · exact qPredicateTranslate_isBoundedLocalNIP
  · exact hgap

/-- The Hilbert--`q` reconstruction formula is NIP in the complete theory of
the bounded `Y`-expansion. The finite continuous-connective closure theorem combines the two named
predicates in every expansion model. -/
theorem reconstructionFormula_isNIPInCompleteTheory
    (R : ℝ) (hR : 0 < R) :
    MultiFormula.IsNIPInCompleteTheory
      (expansionStructure R hR) reconstructionFormula := by
  apply MultiFormula.isNIPInCompleteTheory_connective
  intro j
  fin_cases j
  · exact hilbertFormula_isNIPInCompleteTheory R hR
  · exact qFormula_isNIPInCompleteTheory R hR

/-- On every positive `Y`-ball, the normalized norm formula is NIP in the
complete norm-reduct theory, with reconstruction and reduct transfer both
fully discharged. -/
theorem normFormula_isNIPInCompleteTheory
    (R : ℝ) (hR : 0 < R) :
    MultiFormula.IsNIPInCompleteTheory
      (reductStructure R hR) normFormula :=
  normFormula_isNIPInReduct_of_reconstructionNIP R hR
    (reconstructionFormula_isNIPInCompleteTheory R hR)

end

end NormFormula.HalfGraph.Y.ContinuousLanguage
