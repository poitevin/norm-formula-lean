import NormFormula.Combinatorics.FiniteIPPattern
import NormFormula.Combinatorics.QFatShattering

/-!
# No arbitrarily large bounded IP patterns for `q`

The positive-scale fat-shattering bound for bounded translates of `q`
immediately bounds every finite IP pattern with a fixed positive gap.
-/

namespace NormFormula.HalfGraph

/-- For fixed row and parameter radii and a fixed positive gap, there is a
uniform upper bound on the dimension of every IP pattern for `q(x+y)`. -/
theorem exists_qTranslation_IPPattern_bound
    (R_x R_y low high : ℝ) (hgap : low < high) :
    ∃ N : ℕ, ∀ (n : ℕ) (rows : Fin n → HilbertSpace),
      (∀ r, ‖rows r‖ ≤ R_x) →
      NormFormula.IsIPPattern (qTranslationValue rows R_y) low high → n < N := by
  let ε := (high - low) / 4
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨N, hN⟩ := exists_qTranslation_fatShattering_bound R_x R_y ε hε
  refine ⟨N, ?_⟩
  intro n rows hrows hip
  apply hN n rows hrows
  apply hip.isFatShattered
  dsimp [ε]
  linarith

/-- Equivalently, bounded fixed-gap IP patterns for `q` cannot occur in
every finite dimension. -/
theorem not_qTranslation_IPPatterns_all_dimensions
    (R_x R_y low high : ℝ) (hgap : low < high) :
    ¬ ∀ n : ℕ, ∃ rows : Fin n → HilbertSpace,
      (∀ r, ‖rows r‖ ≤ R_x) ∧
      NormFormula.IsIPPattern (qTranslationValue rows R_y) low high := by
  obtain ⟨N, hN⟩ :=
    exists_qTranslation_IPPattern_bound R_x R_y low high hgap
  intro hall
  obtain ⟨rows, hrows, hip⟩ := hall N
  exact (Nat.lt_irrefl N) (hN N rows hrows hip)

end NormFormula.HalfGraph
