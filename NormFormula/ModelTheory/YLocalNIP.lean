import NormFormula.Analytic.YPredicates
import NormFormula.Combinatorics.QIPPattern
import NormFormula.ModelTheory.LocalNIP

/-!
# Bounded local NIP for `q` on the Hilbert and `Y` sorts

The sparse trace argument is repackaged using the finite-pattern semantic
interface.  Norm comparison then transfers the result to the actual normed
space `Y` and its named `q` predicate.
-/

namespace NormFormula.HalfGraph

/-- Translation by a parameter followed by the seminorm `q` on the underlying
Hilbert model. -/
noncomputable def qSeminormTranslate (x y : HilbertSpace) : ℝ :=
  qSeminorm (x + y)

/-- The sparse trace theorem says exactly that bounded translates of `q` have
bounded local NIP on the Hilbert model. -/
theorem qSeminormTranslate_isBoundedLocalNIP :
    NormFormula.IsBoundedLocalNIP qSeminormTranslate := by
  intro R_x R_y low high hgap
  obtain ⟨N, hN⟩ :=
    exists_qTranslation_IPPattern_bound R_x R_y low high hgap
  refine ⟨N, ?_⟩
  intro n rows hrows hip
  apply hN n rows hrows
  simpa [NormFormula.boundedBinaryValue, qSeminormTranslate,
    qTranslationValue] using hip

namespace Y


/-- Translation followed by the named `q` predicate on the actual `Y` sort. -/
noncomputable def qPredicateTranslate (x y : Y) : ℝ := qPredicate (x + y)

/-- The named `q` predicate has bounded local NIP on the actual normed space
`Y`.  Its proof is the Hilbert result pulled back along the norm-decreasing
identity map. -/
theorem qPredicateTranslate_isBoundedLocalNIP :
    NormFormula.IsBoundedLocalNIP qPredicateTranslate := by
  have hpullback := qSeminormTranslate_isBoundedLocalNIP.comap
    (fun x : Y ↦ x.toHilbert) (fun y : Y ↦ y.toHilbert)
    hilbert_norm_le_norm hilbert_norm_le_norm
  simpa [qPredicateTranslate, qPredicate, qSeminormTranslate] using hpullback


end Y

end NormFormula.HalfGraph
