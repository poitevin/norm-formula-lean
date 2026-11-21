import Mathlib.Analysis.Convex.Uniform
import NormFormula.Analytic.XHilbertEquiv

/-!
# The global augmented norm and uniform convexity of `X`

On the Hilbert sum underlying `XSpace`, the paper defines

`M_oplus(z) = sqrt (∑ n, M_n(z_n)^2)`.

This file bundles `M_oplus` as a seminorm, proves its sharp global bound, and
identifies the actual norm of `XSpace` with the Hilbert norm augmented by this
seminorm.  The general augmented-norm midpoint lemma then gives the paper's
quantitative estimate with constant `1 / 12`, and hence Mathlib's standard
`UniformConvexSpace XSpace` interface.
-/

namespace NormFormula.X

noncomputable section

/-- The scalar `ℓ₂` target in which the block-seminorm values are collected. -/
abbrev ScalarL2 := lp (fun _ : ℕ ↦ ℝ) 2

/-- The sequence of block-seminorm values is square summable. -/
theorem blockSeminormValues_mem (z : XHilbertSpace) :
    Memℓp (fun n ↦ blockSeminorm n (z n)) 2 := by
  apply memℓp_gen
  have hs : Summable (fun n ↦ ‖z n‖ ^ 2) := by
    simpa using (lp.memℓp z).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have hscaled : Summable (fun n ↦ (Real.sqrt 2 * ‖z n‖) ^ 2) := by
    have hm := hs.mul_left ((Real.sqrt 2) ^ 2)
    simpa [mul_pow] using hm
  exact Summable.of_nonneg_of_le
    (fun n ↦ by positivity)
    (fun n ↦ by
      have h := blockSeminorm_le_sqrtTwo_mul_norm (z n)
      norm_num only [ENNReal.toReal_ofNat]
      simpa [Real.rpow_two, pow_two] using
        (Real.rpow_le_rpow (z := (2 : ℝ)) (apply_nonneg _ _) h (by norm_num))) hscaled

/-- The square-summable scalar sequence `(M_n(z_n))_n`. -/
def blockSeminormValues (z : XHilbertSpace) : ScalarL2 :=
  ⟨fun n ↦ blockSeminorm n (z n), blockSeminormValues_mem z⟩

@[simp]
theorem blockSeminormValues_apply (z : XHilbertSpace) (n : ℕ) :
    blockSeminormValues z n = blockSeminorm n (z n) :=
  rfl

/-- The unbundled value of the paper's sum seminorm `M_oplus`. -/
def sumSeminormValue (z : XHilbertSpace) : ℝ :=
  ‖blockSeminormValues z‖

/-- Triangle inequality for `M_oplus`. -/
theorem sumSeminormValue_add_le (x y : XHilbertSpace) :
    sumSeminormValue (x + y) ≤ sumSeminormValue x + sumSeminormValue y := by
  unfold sumSeminormValue
  calc
    ‖blockSeminormValues (x + y)‖ ≤ ‖blockSeminormValues x + blockSeminormValues y‖ := by
      apply lp.norm_le_of_tsum_le (by norm_num : 0 < (2 : ENNReal).toReal)
        (norm_nonneg (blockSeminormValues x + blockSeminormValues y))
      rw [lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal)]
      apply Summable.tsum_le_tsum
      · intro n
        norm_num only [ENNReal.toReal_ofNat]
        have h := map_add_le_add (blockSeminorm n) (x n) (y n)
        apply Real.rpow_le_rpow (norm_nonneg _) ?_ (by norm_num)
        change |blockSeminorm n ((x + y) n)| ≤
          |blockSeminorm n (x n) + blockSeminorm n (y n)|
        rw [abs_of_nonneg (apply_nonneg _ _),
          abs_of_nonneg (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))]
        simpa using h
      · exact (lp.memℓp (blockSeminormValues (x + y))).summable (by norm_num)
      · exact (lp.memℓp (blockSeminormValues x + blockSeminormValues y)).summable (by norm_num)
    _ ≤ ‖blockSeminormValues x‖ + ‖blockSeminormValues y‖ := norm_add_le _ _

/-- Absolute homogeneity of `M_oplus`. -/
theorem sumSeminormValue_smul (r : ℝ) (x : XHilbertSpace) :
    sumSeminormValue (r • x) = ‖r‖ * sumSeminormValue x := by
  have hvec : blockSeminormValues (r • x) = ‖r‖ • blockSeminormValues x := by
    ext n
    simp [map_smul_eq_mul]
  rw [sumSeminormValue, hvec, norm_smul, sumSeminormValue]
  simp

/-- The paper's global seminorm `M_oplus`, bundled as a Mathlib seminorm. -/
noncomputable def sumSeminorm : Seminorm ℝ XHilbertSpace :=
  Seminorm.of sumSeminormValue sumSeminormValue_add_le sumSeminormValue_smul

@[simp]
theorem sumSeminorm_apply (z : XHilbertSpace) :
    sumSeminorm z = ‖blockSeminormValues z‖ :=
  rfl

/-- Squaring `M_oplus` gives the sum of the squared block seminorms. -/
theorem sumSeminorm_sq (z : XHilbertSpace) :
    sumSeminorm z ^ 2 = ∑' n, blockSeminorm n (z n) ^ 2 := by
  rw [sumSeminorm_apply]
  simpa [Real.rpow_two, Real.norm_eq_abs,
    abs_of_nonneg (apply_nonneg (blockSeminorm _) _)] using
    (lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ENNReal).toReal) (blockSeminormValues z))

/-- The bundled seminorm agrees with the square-root formula in the paper. -/
theorem sumSeminorm_eq_sqrt_tsum (z : XHilbertSpace) :
    sumSeminorm z = Real.sqrt (∑' n, blockSeminorm n (z n) ^ 2) := by
  rw [← sumSeminorm_sq]
  exact (Real.sqrt_sq (apply_nonneg sumSeminorm z)).symm

/-- The global bound `M_oplus(z)^2 ≤ 2 * ‖z‖₂^2`. -/
theorem sumSeminorm_sq_le_two_mul_norm_sq (z : XHilbertSpace) :
    sumSeminorm z ^ 2 ≤ 2 * ‖z‖ ^ 2 := by
  rw [sumSeminorm_sq]
  have hs : Summable (fun n ↦ ‖z n‖ ^ 2) := by
    simpa using (lp.memℓp z).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  calc
    ∑' n, blockSeminorm n (z n) ^ 2 ≤ ∑' n, 2 * ‖z n‖ ^ 2 := by
      apply Summable.tsum_le_tsum
      · intro n
        exact blockSeminorm_sq_le_two_mul_norm_sq (z n)
      · have hm : Summable (fun n ↦ blockSeminorm n (z n) ^ 2) := by
          simpa [Real.rpow_two, Real.norm_eq_abs,
            abs_of_nonneg (apply_nonneg (blockSeminorm _) _)] using
            (lp.memℓp (blockSeminormValues z)).summable
              (by norm_num : 0 < (2 : ENNReal).toReal)
        exact hm
      · exact hs.mul_left 2
    _ = 2 * ∑' n, ‖z n‖ ^ 2 := hs.tsum_mul_left 2
    _ = 2 * ‖z‖ ^ 2 := by
      have hz : ‖z‖ ^ (2 : ℕ) = ∑' n, ‖z n‖ ^ 2 := by
        simpa [Real.rpow_two] using
          (lp.norm_rpow_eq_tsum
            (by norm_num : 0 < (2 : ENNReal).toReal) z)
      rw [hz]

/-- The actual norm of `XSpace` has the paper's global square decomposition. -/
theorem norm_sq_eq_hilbert_add_sumSeminorm_sq (x : XSpace) :
    ‖x‖ ^ 2 = ‖toHilbert x‖ ^ 2 + sumSeminorm (toHilbert x) ^ 2 := by
  have hxnorm : ‖x‖ ^ 2 = ∑' n, ‖x n‖ ^ 2 := by
    simpa [Real.rpow_two] using
      (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) x)
  have hhilbert : ‖toHilbert x‖ ^ 2 = ∑' n, ‖toHilbert x n‖ ^ 2 := by
    simpa [Real.rpow_two] using
      (lp.norm_rpow_eq_tsum
        (by norm_num : 0 < (2 : ENNReal).toReal) (toHilbert x))
  have hsHilbert : Summable (fun n ↦ ‖toHilbert x n‖ ^ 2) := by
    simpa using (lp.memℓp (toHilbert x)).summable
      (by norm_num : 0 < (2 : ENNReal).toReal)
  have hsSeminorm : Summable (fun n ↦ blockSeminorm n (toHilbert x n) ^ 2) := by
    simpa [Real.rpow_two, Real.norm_eq_abs,
      abs_of_nonneg (apply_nonneg (blockSeminorm _) _)] using
      (lp.memℓp (blockSeminormValues (toHilbert x))).summable
        (by norm_num : 0 < (2 : ENNReal).toReal)
  rw [hxnorm, hhilbert, sumSeminorm_sq]
  calc
    ∑' n, ‖x n‖ ^ 2 =
        ∑' n, (‖toHilbert x n‖ ^ 2 + blockSeminorm n (toHilbert x n) ^ 2) := by
      apply tsum_congr
      intro n
      change blockNorm (toHilbert x n) ^ 2 = _
      exact augmentedNorm_sq (blockSeminorm n) (toHilbert x n)
    _ = (∑' n, ‖toHilbert x n‖ ^ 2) +
        ∑' n, blockSeminorm n (toHilbert x n) ^ 2 :=
      Summable.tsum_add hsHilbert hsSeminorm

/-- The norm of `XSpace` is exactly the Hilbert norm augmented by `M_oplus`. -/
theorem norm_eq_augmentedNorm_toHilbert (x : XSpace) :
    ‖x‖ = augmentedNorm sumSeminorm (toHilbert x) := by
  have hsquares : ‖x‖ ^ 2 = augmentedNorm sumSeminorm (toHilbert x) ^ 2 := by
    rw [augmentedNorm_sq, norm_sq_eq_hilbert_add_sumSeminorm_sq]
  nlinarith [norm_nonneg x, augmentedNorm_nonneg sumSeminorm (toHilbert x)]

/-- The quantitative midpoint estimate asserted for `X` in the main theorem. -/
theorem norm_midpoint_sq_le {x y : XSpace} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 ≤
      1 - (1 / 12 : ℝ) * ‖x - y‖ ^ 2 := by
  have hx' : augmentedNorm sumSeminorm (toHilbert x) ≤ 1 := by
    rw [← norm_eq_augmentedNorm_toHilbert]
    exact hx
  have hy' : augmentedNorm sumSeminorm (toHilbert y) ≤ 1 := by
    rw [← norm_eq_augmentedNorm_toHilbert]
    exact hy
  rw [norm_eq_augmentedNorm_toHilbert, norm_eq_augmentedNorm_toHilbert]
  change augmentedNorm sumSeminorm
      ((1 / 2 : ℝ) • (toHilbert x + toHilbert y)) ^ 2 ≤
    1 - (1 / 12 : ℝ) *
      augmentedNorm sumSeminorm (toHilbert x - toHilbert y) ^ 2
  exact augmentedNorm_midpoint_sq_le sumSeminorm
    sumSeminorm_sq_le_two_mul_norm_sq hx' hy'

/-- The explicit midpoint estimate supplies Mathlib's uniform-convexity interface for `XSpace`. -/
noncomputable instance : UniformConvexSpace XSpace where
  uniform_convex {ε} hε := by
    let δ : ℝ := min 1 (ε ^ 2 / 12)
    have hδ : 0 < δ := by
      exact lt_min one_pos (div_pos (sq_pos_of_pos hε) (by norm_num))
    refine ⟨δ, hδ, ?_⟩
    intro x hx y hy hxy
    by_cases hεtwo : ε ≤ 2
    · have hmid := norm_midpoint_sq_le hx.le hy.le
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hmid
      have hsum_nonneg : 0 ≤ ‖x + y‖ := norm_nonneg _
      have hsum_le_two : ‖x + y‖ ≤ 2 := by
        calc
          ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
          _ = 2 := by rw [hx, hy]; norm_num
      have hdist_nonneg : 0 ≤ ‖x - y‖ := norm_nonneg _
      have heps_sq_le : ε ^ 2 ≤ ‖x - y‖ ^ 2 :=
        (sq_le_sq₀ hε.le hdist_nonneg).2 hxy
      have heps_sq_le_four : ε ^ 2 ≤ 4 := by
        nlinarith [sq_nonneg (2 - ε)]
      have htarget_nonneg : 0 ≤ 2 - ε ^ 2 / 12 := by nlinarith
      have hsquares : ‖x + y‖ ^ 2 ≤ (2 - ε ^ 2 / 12) ^ 2 := by
        nlinarith [sq_nonneg (ε ^ 2)]
      have hstrong : ‖x + y‖ ≤ 2 - ε ^ 2 / 12 :=
        (sq_le_sq₀ hsum_nonneg htarget_nonneg).mp hsquares
      have hδle : δ ≤ ε ^ 2 / 12 := min_le_right _ _
      linarith
    · have hdist_le_two : ‖x - y‖ ≤ 2 := by
        calc
          ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
          _ = 2 := by rw [hx, hy]; norm_num
      exact (hεtwo (hxy.trans hdist_le_two)).elim

end

end NormFormula.X
