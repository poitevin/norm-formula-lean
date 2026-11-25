import NormFormula.ContinuousLogic.AugmentedNormTheoryNIP
import NormFormula.ModelTheory.ConnectiveClosure
import NormFormula.ModelTheory.YLocalNIP

/-!
# Bounded local NIP for the `Y`-norm

The public theorem applies the general Hilbert--seminorm criterion: transfer
the Hilbert predicate, use Hilbert stability, combine the predicates by a
continuous connective, and descend through finite-box compactness.
-/

namespace NormFormula.HalfGraph.Y

/-- Translation followed by the actual ambient norm on `Y`. -/
noncomputable def normPredicateTranslate (x y : Y) : ℝ := ‖x + y‖


/-- The actual `Y`-norm translation predicate has bounded local NIP by the
general quadratic Hilbert--seminorm criterion. -/
theorem normPredicateTranslate_isBoundedLocalNIP :
    NormFormula.IsBoundedLocalNIP normPredicateTranslate :=
  NormFormula.ContinuousLogic.quadratic_norm_isBoundedLocalNIP
    linearEquivHilbert.toLinearMap hilbert_norm_le_norm
    (qSeminorm.comp linearEquivHilbert.toLinearMap) qPredicate_le_norm
    norm_sq_eq_predicates qPredicateTranslate_isBoundedLocalNIP

end NormFormula.HalfGraph.Y
