import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Seminorm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import NormFormula.Analytic.AugmentedNorm

/-!
# The ordered-pair seminorm on two copies of `ℓ₂(ℕ)`

This is the analytic core of the paper's space `Y`.  We define

`q(u, v) = sup { |u i + v j| : i < j }`

as a supremum of bundled coordinate seminorms and prove
`q z ≤ sqrt 2 * ‖z‖` for the Hilbertian product norm.
-/

namespace NormFormula.HalfGraph

open scoped ENNReal NNReal

/-- Real square-summable sequences indexed by the natural numbers. -/
abbrev RealL2 := lp (fun _ : ℕ => ℝ) 2

/-- The Hilbertian product `ℓ₂(ℕ) ⊕₂ ℓ₂(ℕ)`. -/
abbrev HilbertSpace := WithLp 2 (RealL2 × RealL2)

/-- An admissible ordered pair of coordinates. -/
abbrev OrderedPair := {p : ℕ × ℕ // p.1 < p.2}

/-- The absolute value of the `(i,j)` coordinate functional. -/
noncomputable def pairSeminorm (i j : ℕ) : Seminorm ℝ HilbertSpace :=
  Seminorm.of
    (fun z => |z.fst i + z.snd j|)
    (fun x y => by
      dsimp only
      rw [show (x + y).fst i = x.fst i + y.fst i by
        exact congrFun (lp.coeFn_add x.fst y.fst) i]
      rw [show (x + y).snd j = x.snd j + y.snd j by
        exact congrFun (lp.coeFn_add x.snd y.snd) j]
      convert abs_add_le (x.fst i + x.snd j) (y.fst i + y.snd j) using 1
      ring_nf)
    (fun r x => by
      simp only [WithLp.smul_fst, WithLp.smul_snd, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      rw [← mul_add, abs_mul, Real.norm_eq_abs])

@[simp]
theorem pairSeminorm_apply (i j : ℕ) (z : HilbertSpace) :
    pairSeminorm i j z = |z.fst i + z.snd j| := rfl

/-- Every coordinate functional is bounded by `sqrt 2` times the Hilbert norm. -/
theorem pairSeminorm_le_sqrtTwo_mul_norm (i j : ℕ) (z : HilbertSpace) :
    pairSeminorm i j z ≤ Real.sqrt 2 * ‖z‖ := by
  have hui : |z.fst i| ≤ ‖z.fst‖ := by
    simpa [Real.norm_eq_abs] using
      lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) z.fst i
  have hvj : |z.snd j| ≤ ‖z.snd‖ := by
    simpa [Real.norm_eq_abs] using
      lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) z.snd j
  have hprod : ‖z‖ ^ 2 = ‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2 :=
    WithLp.prod_norm_sq_eq_of_L2 z
  have hpair : |z.fst i + z.snd j| ≤ |z.fst i| + |z.snd j| := abs_add_le _ _
  have hsquare : |z.fst i + z.snd j| ^ 2 ≤ 2 * ‖z‖ ^ 2 := by
    nlinarith [abs_nonneg (z.fst i + z.snd j), abs_nonneg (z.fst i),
      abs_nonneg (z.snd j), norm_nonneg z.fst, norm_nonneg z.snd,
      sq_nonneg (|z.fst i| - |z.snd j|)]
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 * ‖z‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hsqrt_sq : (Real.sqrt 2 * ‖z‖) ^ 2 = 2 * ‖z‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  rw [pairSeminorm_apply]
  nlinarith [abs_nonneg (z.fst i + z.snd j)]

/-- The coordinate seminorm associated to an admissible pair. -/
noncomputable def orderedPairSeminorm (p : OrderedPair) : Seminorm ℝ HilbertSpace :=
  pairSeminorm p.1.1 p.1.2

/-- The set of admissible pairs is nonempty (`0 < 1`). -/
noncomputable instance : Nonempty OrderedPair :=
  ⟨⟨(0, 1), by norm_num⟩⟩

/-- The admissible coordinate seminorms have a common seminorm upper bound. -/
theorem orderedPairSeminorm_bddAbove :
    BddAbove (Set.range orderedPairSeminorm) := by
  refine ⟨(2 : ℝ≥0) • normSeminorm ℝ HilbertSpace, ?_⟩
  rintro _ ⟨p, rfl⟩ z
  change pairSeminorm p.1.1 p.1.2 z ≤ 2 * ‖z‖
  have hp := pairSeminorm_le_sqrtTwo_mul_norm p.1.1 p.1.2 z
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  exact hp.trans (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg z))

/-- The ordered-pair seminorm `q(u,v) = sup_{i<j} |u_i + v_j|`. -/
noncomputable def qSeminorm : Seminorm ℝ HilbertSpace :=
  ⨆ p : OrderedPair, orderedPairSeminorm p

/-- Pointwise formula for the ordered-pair seminorm. -/
theorem qSeminorm_apply (z : HilbertSpace) :
    qSeminorm z = ⨆ p : OrderedPair, |z.fst p.1.1 + z.snd p.1.2| := by
  rw [qSeminorm, Seminorm.iSup_apply orderedPairSeminorm_bddAbove]
  rfl

/-- The supremum retains the common sharp `sqrt 2` bound. -/
theorem qSeminorm_le_sqrtTwo_mul_norm (z : HilbertSpace) :
    qSeminorm z ≤ Real.sqrt 2 * ‖z‖ := by
  rw [qSeminorm_apply]
  refine ciSup_le fun p => ?_
  exact pairSeminorm_le_sqrtTwo_mul_norm p.1.1 p.1.2 z

/-- Squared form of the bound, exactly matching the hypothesis of `augmentedNorm`. -/
theorem qSeminorm_sq_le_two_mul_norm_sq (z : HilbertSpace) :
    qSeminorm z ^ 2 ≤ 2 * ‖z‖ ^ 2 := by
  have hq := qSeminorm_le_sqrtTwo_mul_norm z
  have hq_nonneg : 0 ≤ qSeminorm z := by positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 * ‖z‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hsqrt_sq : (Real.sqrt 2 * ‖z‖) ^ 2 = 2 * ‖z‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  nlinarith

/-- The paper's renorming of the Hilbertian product. -/
noncomputable def yNorm (z : HilbertSpace) : ℝ :=
  augmentedNorm qSeminorm z

/-- The original Hilbert norm is bounded by the `Y`-norm. -/
theorem norm_le_yNorm (z : HilbertSpace) : ‖z‖ ≤ yNorm z :=
  norm_le_augmentedNorm qSeminorm z

/-- The ordered-pair seminorm is bounded by the `Y`-norm. -/
theorem qSeminorm_le_yNorm (z : HilbertSpace) : qSeminorm z ≤ yNorm z :=
  seminorm_le_augmentedNorm qSeminorm z

/-- The `Y`-norm is at most `sqrt 3` times the Hilbert norm. -/
theorem yNorm_le_sqrtThree_mul_norm (z : HilbertSpace) :
    yNorm z ≤ Real.sqrt 3 * ‖z‖ :=
  augmentedNorm_le_sqrtThree_mul qSeminorm qSeminorm_sq_le_two_mul_norm_sq z

/-- The quantitative uniform-convexity estimate specialized to the `Y`-norm. -/
theorem yNorm_midpoint_sq_le {x y : HilbertSpace}
    (hx : yNorm x ≤ 1) (hy : yNorm y ≤ 1) :
    yNorm ((1 / 2 : ℝ) • (x + y)) ^ 2 ≤
      1 - (1 / 12 : ℝ) * yNorm (x - y) ^ 2 :=
  augmentedNorm_midpoint_sq_le qSeminorm qSeminorm_sq_le_two_mul_norm_sq hx hy


end NormFormula.HalfGraph
