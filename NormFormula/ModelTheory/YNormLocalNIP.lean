import NormFormula.ContinuousLogic.AugmentedNormTheoryNIP
import NormFormula.ModelTheory.ConnectiveClosure
import NormFormula.ModelTheory.YLocalNIP

/-!
# Bounded local NIP for the `Y`-norm

The public theorem applies the general Hilbert--seminorm criterion: transfer
the Hilbert predicate, use Hilbert stability, combine the predicates by a
continuous connective, and descend through finite-box compactness. The older
quantitative Euclidean closure interface remains supplementary.
-/

namespace NormFormula.HalfGraph.Y

/-- Translation followed by the actual ambient norm on `Y`. -/
noncomputable def normPredicateTranslate (x y : Y) : ℝ := ‖x + y‖

/-- The Hilbert translation predicate is bounded on every pair of `Y`-balls. -/
theorem hilbertNormPredicateTranslate_boundedOnNormBalls :
    NormFormula.IsBoundedOnNormBalls hilbertNormPredicateTranslate := by
  intro R_x R_y
  refine ⟨|R_x| + |R_y|, ?_⟩
  intro x y hx hy
  have hx' : ‖x‖ ≤ |R_x| := hx.trans (le_abs_self R_x)
  have hy' : ‖y‖ ≤ |R_y| := hy.trans (le_abs_self R_y)
  rw [hilbertNormPredicateTranslate,
    abs_of_nonneg (hilbertNormPredicate_nonneg (x + y))]
  exact (hilbertNormPredicate_le_norm (x + y)).trans
    ((norm_add_le x y).trans (add_le_add hx' hy'))

/-- The `q` translation predicate is bounded on every pair of `Y`-balls. -/
theorem qPredicateTranslate_boundedOnNormBalls :
    NormFormula.IsBoundedOnNormBalls qPredicateTranslate := by
  intro R_x R_y
  refine ⟨|R_x| + |R_y|, ?_⟩
  intro x y hx hy
  have hx' : ‖x‖ ≤ |R_x| := hx.trans (le_abs_self R_x)
  have hy' : ‖y‖ ≤ |R_y| := hy.trans (le_abs_self R_y)
  rw [qPredicateTranslate, abs_of_nonneg (qPredicate_nonneg (x + y))]
  exact (qPredicate_le_norm (x + y)).trans
    ((norm_add_le x y).trans (add_le_add hx' hy'))

/-- Pointwise reduction of the norm translation predicate to the Euclidean
connective applied to the two named predicates. -/
theorem normPredicateTranslate_eq_connective (x y : Y) :
    normPredicateTranslate x y =
      NormFormula.euclideanConnective
        (hilbertNormPredicateTranslate x y) (qPredicateTranslate x y) := by
  exact norm_eq_sqrt_predicates (x + y)

/-- A supplied binary-connective closure theorem yields bounded local NIP for
the actual `Y`-norm translation predicate. -/
theorem normPredicateTranslate_isBoundedLocalNIP_of_connectiveClosure
    (hclosure : NormFormula.PreservesBoundedLocalNIP₂
      NormFormula.euclideanConnective) :
    NormFormula.IsBoundedLocalNIP normPredicateTranslate := by
  have h : NormFormula.IsBoundedLocalNIP
      (fun x y : Y ↦ NormFormula.euclideanConnective
        (hilbertNormPredicateTranslate x y) (qPredicateTranslate x y)) :=
    hclosure (X := Y) (Y := Y)
      hilbertNormPredicateTranslate qPredicateTranslate
      hilbertNormPredicateTranslate_boundedOnNormBalls
      qPredicateTranslate_boundedOnNormBalls
      hilbertNormPredicateTranslate_isBoundedLocalNIP
      qPredicateTranslate_isBoundedLocalNIP
  simpa [normPredicateTranslate, NormFormula.euclideanConnective,
    hilbertNormPredicateTranslate, qPredicateTranslate,
    hilbertNormPredicate, qPredicate] using h

/-- The actual `Y`-norm translation predicate has bounded local NIP by the
general quadratic Hilbert--seminorm criterion. -/
theorem normPredicateTranslate_isBoundedLocalNIP :
    NormFormula.IsBoundedLocalNIP normPredicateTranslate :=
  NormFormula.ContinuousLogic.quadratic_norm_isBoundedLocalNIP
    linearEquivHilbert.toLinearMap hilbert_norm_le_norm
    (qSeminorm.comp linearEquivHilbert.toLinearMap) qPredicate_le_norm
    norm_sq_eq_predicates qPredicateTranslate_isBoundedLocalNIP

end NormFormula.HalfGraph.Y
