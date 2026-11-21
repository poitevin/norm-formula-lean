import Mathlib.Analysis.InnerProductSpace.ProdL2
import NormFormula.Analytic.XHilbertEquiv
import NormFormula.Analytic.XYSpace

/-!
# The global Hilbert model of `X ⊕₂ Y`

The established equivalences for `XSpace` and `Y` are applied
coordinatewise. Their common forward constant `1` and inverse constant
`√3` pass unchanged to the ℓ₂-product, giving the quantitative Hilbert
equivalence asserted in the direct-sum corollary.
-/

namespace NormFormula.XY

noncomputable section

open scoped InnerProductSpace ENNReal

/-- The Hilbert ℓ₂-product underlying the renormed direct sum. -/
abbrev XYHilbertSpace :=
  WithLp 2 (X.XHilbertSpace × HalfGraph.HilbertSpace)

/-- Apply the two factor identities into their Hilbert models. -/
def toHilbert (z : XYSpace) : XYHilbertSpace :=
  WithLp.toLp 2
    (X.linearEquivHilbertSum z.fst,
      HalfGraph.Y.linearEquivHilbert z.snd)

/-- Apply the inverse factor identities to a vector in the Hilbert model. -/
def ofHilbert (z : XYHilbertSpace) : XYSpace :=
  WithLp.toLp 2
    (X.linearEquivHilbertSum.symm z.fst,
      HalfGraph.Y.linearEquivHilbert.symm z.snd)

@[simp]
theorem toHilbert_fst (z : XYSpace) :
    (toHilbert z).fst = X.toHilbert z.fst := rfl

@[simp]
theorem toHilbert_snd (z : XYSpace) :
    (toHilbert z).snd = z.snd.toHilbert := rfl

@[simp]
theorem ofHilbert_fst (z : XYHilbertSpace) :
    (ofHilbert z).fst = X.ofHilbert z.fst := rfl

@[simp]
theorem ofHilbert_snd (z : XYHilbertSpace) :
    (ofHilbert z).snd = HalfGraph.Y.linearEquivHilbert.symm z.snd := rfl

/-- The algebraic coordinatewise equivalence. -/
def linearEquivHilbertSum : XYSpace ≃ₗ[ℝ] XYHilbertSpace where
  toFun := toHilbert
  invFun := ofHilbert
  left_inv z := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact X.linearEquivHilbertSum.symm_apply_apply z.fst
    · exact HalfGraph.Y.linearEquivHilbert.symm_apply_apply z.snd
  right_inv z := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact X.linearEquivHilbertSum.apply_symm_apply z.fst
    · exact HalfGraph.Y.linearEquivHilbert.apply_symm_apply z.snd
  map_add' z w := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact X.linearEquivHilbertSum.map_add z.fst w.fst
    · exact HalfGraph.Y.linearEquivHilbert.map_add z.snd w.snd
  map_smul' c z := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact X.linearEquivHilbertSum.map_smul c z.fst
    · exact HalfGraph.Y.linearEquivHilbert.map_smul c z.snd

@[simp]
theorem linearEquivHilbertSum_apply (z : XYSpace) :
    linearEquivHilbertSum z = toHilbert z := rfl

@[simp]
theorem linearEquivHilbertSum_symm_apply (z : XYHilbertSpace) :
    linearEquivHilbertSum.symm z = ofHilbert z := rfl

/-- The forward coordinatewise map does not increase the norm. -/
theorem norm_toHilbert_le (z : XYSpace) :
    ‖toHilbert z‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2 (toHilbert z),
    WithLp.prod_norm_sq_eq_of_L2 z]
  simp only [toHilbert_fst, toHilbert_snd]
  exact add_le_add
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (X.norm_toHilbert_le z.fst))
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (HalfGraph.Y.hilbert_norm_le_norm z.snd))

/-- The inverse coordinatewise map increases the norm by at most `√3`. -/
theorem norm_ofHilbert_le (z : XYHilbertSpace) :
    ‖ofHilbert z‖ ≤ Real.sqrt 3 * ‖z‖ := by
  have hx : ‖(ofHilbert z).fst‖ ≤ Real.sqrt 3 * ‖z.fst‖ := by
    simpa using X.norm_ofHilbert_le z.fst
  have hy : ‖(ofHilbert z).snd‖ ≤ Real.sqrt 3 * ‖z.snd‖ := by
    simpa using HalfGraph.Y.norm_le_sqrtThree_mul_hilbert_norm
      (HalfGraph.Y.linearEquivHilbert.symm z.snd)
  have hxSq := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr hx
  have hySq := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr hy
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [WithLp.prod_norm_sq_eq_of_L2 (ofHilbert z), mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
    WithLp.prod_norm_sq_eq_of_L2 z]
  simp only [ofHilbert_fst, ofHilbert_snd]
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at hxSq hySq
  simp only [ofHilbert_fst, ofHilbert_snd] at hxSq hySq
  nlinarith

/-- The direct sum is continuously linearly equivalent to an actual Hilbert
space, with forward bound `1` and inverse bound `√3`. -/
noncomputable def continuousLinearEquivHilbertSum :
    XYSpace ≃L[ℝ] XYHilbertSpace :=
  linearEquivHilbertSum.toContinuousLinearEquivOfBounds 1 (Real.sqrt 3)
    (fun z ↦ by simpa using norm_toHilbert_le z)
    (fun z ↦ by simpa using norm_ofHilbert_le z)

end

end NormFormula.XY
