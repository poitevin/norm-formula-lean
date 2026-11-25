import NormFormula.Analytic.YSpace

/-!
# The Hilbert and `q` predicates on `Y`

The model-theoretic argument expands the Banach structure `Y` by the
underlying Hilbert norm and by `q`.  Here both are packaged as real-valued
functions on the actual normed space `Y`.  Each is `1`-Lipschitz for the
`Y`-metric, and their Euclidean combination recovers the ambient norm.
-/

namespace NormFormula.HalfGraph.Y

/-- The original Hilbert norm, regarded as a predicate on `Y`. -/
noncomputable def hilbertNormPredicate (z : Y) : ℝ := ‖z.toHilbert‖

/-- The ordered-pair seminorm, regarded as a predicate on `Y`. -/
noncomputable def qPredicate (z : Y) : ℝ := qSeminorm z.toHilbert


/-- The `q` predicate is bounded by the ambient `Y`-norm. -/
theorem qPredicate_le_norm (z : Y) : qPredicate z ≤ ‖z‖ :=
  qSeminorm_le_yNorm z.toHilbert


/-- The two named predicates reconstruct the square of the ambient norm. -/
@[simp]
theorem norm_sq_eq_predicates (z : Y) :
    ‖z‖ ^ 2 = hilbertNormPredicate z ^ 2 + qPredicate z ^ 2 := by
  exact augmentedNorm_sq qSeminorm z.toHilbert


end NormFormula.HalfGraph.Y
