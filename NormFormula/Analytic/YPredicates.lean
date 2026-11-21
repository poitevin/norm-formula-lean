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

theorem hilbertNormPredicate_nonneg (z : Y) : 0 ≤ hilbertNormPredicate z :=
  norm_nonneg _

theorem qPredicate_nonneg (z : Y) : 0 ≤ qPredicate z := by
  exact apply_nonneg qSeminorm z.toHilbert

/-- The Hilbert predicate is bounded by the ambient `Y`-norm. -/
theorem hilbertNormPredicate_le_norm (z : Y) : hilbertNormPredicate z ≤ ‖z‖ :=
  hilbert_norm_le_norm z

/-- The `q` predicate is bounded by the ambient `Y`-norm. -/
theorem qPredicate_le_norm (z : Y) : qPredicate z ≤ ‖z‖ :=
  qSeminorm_le_yNorm z.toHilbert

/-- Reverse triangle inequality for the Hilbert predicate in the `Y`-metric. -/
theorem abs_hilbertNormPredicate_sub_le (x y : Y) :
    |hilbertNormPredicate x - hilbertNormPredicate y| ≤ ‖x - y‖ := by
  calc
    |hilbertNormPredicate x - hilbertNormPredicate y| ≤
        ‖x.toHilbert - y.toHilbert‖ :=
      abs_norm_sub_norm_le x.toHilbert y.toHilbert
    _ ≤ ‖x - y‖ := by
      simpa [sub_eq_add_neg] using hilbert_norm_le_norm (x - y)

/-- Reverse triangle inequality for `q` in the `Y`-metric. -/
theorem abs_qPredicate_sub_le (x y : Y) :
    |qPredicate x - qPredicate y| ≤ ‖x - y‖ := by
  calc
    |qPredicate x - qPredicate y| =
        ‖qSeminorm x.toHilbert - qSeminorm y.toHilbert‖ := by
      simp only [qPredicate, Real.norm_eq_abs]
    _ ≤ qSeminorm (x.toHilbert - y.toHilbert) :=
      qSeminorm.norm_sub_map_le_sub x.toHilbert y.toHilbert
    _ ≤ yNorm (x.toHilbert - y.toHilbert) :=
      qSeminorm_le_yNorm (x.toHilbert - y.toHilbert)
    _ = ‖x - y‖ := by
      rfl

/-- The Hilbert norm predicate is `1`-Lipschitz on `Y`. -/
theorem hilbertNormPredicate_lipschitz :
    LipschitzWith 1 hilbertNormPredicate := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [Real.dist_eq, dist_eq_norm] using abs_hilbertNormPredicate_sub_le x y

/-- The `q` predicate is `1`-Lipschitz on `Y`. -/
theorem qPredicate_lipschitz : LipschitzWith 1 qPredicate := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [Real.dist_eq, dist_eq_norm] using abs_qPredicate_sub_le x y

/-- Uniform continuity of the named Hilbert predicate. -/
theorem hilbertNormPredicate_uniformContinuous :
    UniformContinuous hilbertNormPredicate :=
  hilbertNormPredicate_lipschitz.uniformContinuous

/-- Uniform continuity of the named `q` predicate. -/
theorem qPredicate_uniformContinuous : UniformContinuous qPredicate :=
  qPredicate_lipschitz.uniformContinuous

/-- The two named predicates reconstruct the square of the ambient norm. -/
@[simp]
theorem norm_sq_eq_predicates (z : Y) :
    ‖z‖ ^ 2 = hilbertNormPredicate z ^ 2 + qPredicate z ^ 2 := by
  exact augmentedNorm_sq qSeminorm z.toHilbert

/-- Equivalent connective form of the norm reconstruction identity. -/
theorem norm_eq_sqrt_predicates (z : Y) :
    ‖z‖ = Real.sqrt (hilbertNormPredicate z ^ 2 + qPredicate z ^ 2) := by
  rfl

end NormFormula.HalfGraph.Y
