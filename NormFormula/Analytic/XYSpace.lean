import Mathlib.Analysis.Normed.Lp.ProdLp
import NormFormula.Analytic.XSpace
import NormFormula.Analytic.YSpace

/-!
# The direct sum `X ⊕₂ Y`

This file constructs the normed space used in the paper's direct-sum
consequence.  It also records the two canonical coordinate embeddings and
their exact norm behavior, so later geometric and model-theoretic arguments
can use the same concrete space.
-/

namespace NormFormula.XY

open scoped ENNReal

/-- The paper's direct sum of `XSpace` and `Y`, equipped with the ℓ₂-product norm. -/
abbrev XYSpace := WithLp 2 (X.XSpace × HalfGraph.Y)

/-- The canonical embedding of `XSpace` into the first summand. -/
noncomputable def inX (x : X.XSpace) : XYSpace :=
  WithLp.toLp 2 (x, 0)

/-- The canonical embedding of `Y` into the second summand. -/
noncomputable def inY (y : HalfGraph.Y) : XYSpace :=
  WithLp.toLp 2 (0, y)


/-- The first coordinate embedding is isometric. -/
@[simp]
theorem norm_inX (x : X.XSpace) : ‖inX x‖ = ‖x‖ := by
  exact WithLp.norm_toLp_fst 2 X.XSpace HalfGraph.Y x

/-- The second coordinate embedding is isometric. -/
@[simp]
theorem norm_inY (y : HalfGraph.Y) : ‖inY y‖ = ‖y‖ := by
  exact WithLp.norm_toLp_snd 2 X.XSpace HalfGraph.Y y

@[simp]
theorem inX_add (x x' : X.XSpace) : inX (x + x') = inX x + inX x' := by
  simp only [inX, ← WithLp.toLp_add, Prod.mk_add_mk, zero_add]

@[simp]
theorem inY_add (y y' : HalfGraph.Y) : inY (y + y') = inY y + inY y' := by
  simp only [inY, ← WithLp.toLp_add, Prod.mk_add_mk, zero_add]

end NormFormula.XY
