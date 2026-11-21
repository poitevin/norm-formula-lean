import Mathlib.Analysis.InnerProductSpace.l2Space
import NormFormula.Analytic.XSpace

/-!
# The global Hilbert model of `XSpace`

The paper's space `XSpace` is the dependent `ℓ₂`-sum of the renormed finite
dimensional spaces `BlockSpace n`.  Each block is uniformly equivalent to its
Euclidean model `BlockHilbert n`.  This file lifts those coordinatewise
equivalences to the full dependent sums.

The resulting continuous linear equivalence has the same uniform constants:
its forward map has norm at most `1`, and its inverse has norm at most `√3`.
In particular, `XSpace` is linearly homeomorphic to an actual Hilbert space.
-/

namespace NormFormula.X

noncomputable section

/-- The Hilbert `ℓ₂`-sum underlying the paper's renormed space `XSpace`. -/
abbrev XHilbertSpace := lp (fun n : ℕ ↦ BlockHilbert n) 2

/-- Applying the blockwise identity into the Hilbert models preserves
square summability. -/
theorem toHilbert_mem (x : XSpace) :
    Memℓp (fun n ↦ (x n).toHilbert) 2 := by
  apply memℓp_gen
  have hs : Summable (fun n ↦ ‖x n‖ ^ 2) := by
    simpa using (lp.memℓp x).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  exact Summable.of_nonneg_of_le
    (fun n ↦ by positivity)
    (fun n ↦ by
      have h := BlockSpace.hilbert_norm_le_norm (x n)
      norm_num only [ENNReal.toReal_ofNat]
      simpa [Real.rpow_two, pow_two] using
        (Real.rpow_le_rpow (z := (2 : ℝ)) (norm_nonneg _) h (by norm_num))) hs

/-- Applying the inverses of the blockwise identities preserves square
summability. -/
theorem ofHilbert_mem (x : XHilbertSpace) :
    Memℓp (fun n ↦ (BlockSpace.linearEquivHilbert n).symm (x n)) 2 := by
  apply memℓp_gen
  have hs : Summable (fun n ↦ ‖x n‖ ^ 2) := by
    simpa using (lp.memℓp x).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have hscaled : Summable (fun n ↦ (Real.sqrt 3 * ‖x n‖) ^ 2) := by
    have hm := hs.mul_left ((Real.sqrt 3) ^ 2)
    simpa [mul_pow] using hm
  exact Summable.of_nonneg_of_le
    (fun n ↦ by positivity)
    (fun n ↦ by
      have h := BlockSpace.norm_le_sqrtThree_mul_hilbert_norm
        ((BlockSpace.linearEquivHilbert n).symm (x n))
      have h' : ‖(BlockSpace.linearEquivHilbert n).symm (x n)‖ ≤
          Real.sqrt 3 * ‖x n‖ := by
        simpa using h
      norm_num only [ENNReal.toReal_ofNat]
      simpa [Real.rpow_two, pow_two] using
        (Real.rpow_le_rpow (z := (2 : ℝ)) (norm_nonneg _) h' (by norm_num))) hscaled

/-- The coordinatewise identity from `XSpace` to its Hilbert model. -/
def toHilbert (x : XSpace) : XHilbertSpace :=
  ⟨fun n ↦ (x n).toHilbert, toHilbert_mem x⟩

/-- The coordinatewise identity from the Hilbert model back to `XSpace`. -/
def ofHilbert (x : XHilbertSpace) : XSpace :=
  ⟨fun n ↦ (BlockSpace.linearEquivHilbert n).symm (x n), ofHilbert_mem x⟩

@[simp]
theorem toHilbert_apply (x : XSpace) (n : ℕ) :
    toHilbert x n = (x n).toHilbert :=
  rfl

@[simp]
theorem ofHilbert_apply (x : XHilbertSpace) (n : ℕ) :
    ofHilbert x n = (BlockSpace.linearEquivHilbert n).symm (x n) :=
  rfl

/-- The algebraic equivalence between `XSpace` and its Hilbert `ℓ₂` model. -/
def linearEquivHilbertSum : XSpace ≃ₗ[ℝ] XHilbertSpace where
  toFun := toHilbert
  invFun := ofHilbert
  left_inv x := by ext n; rfl
  right_inv x := by ext n; rfl
  map_add' x y := by ext n; rfl
  map_smul' c x := by ext n; rfl

/-- The global forward map does not increase the norm. -/
theorem norm_toHilbert_le (x : XSpace) : ‖toHilbert x‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num : 0 < (2 : ENNReal).toReal) (norm_nonneg x)
  rw [lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal)]
  apply Summable.tsum_le_tsum
  · intro n
    norm_num only [ENNReal.toReal_ofNat]
    simpa [Real.rpow_two, pow_two] using
      (Real.rpow_le_rpow (z := (2 : ℝ)) (norm_nonneg ((x n).toHilbert))
        (BlockSpace.hilbert_norm_le_norm (x n)) (by norm_num))
  · exact (lp.memℓp (toHilbert x)).summable (by norm_num)
  · simpa using (lp.memℓp x).summable (by norm_num : 0 < (2 : ENNReal).toReal)

/-- The inverse global map increases the norm by at most `√3`. -/
theorem norm_ofHilbert_le (x : XHilbertSpace) :
    ‖ofHilbert x‖ ≤ Real.sqrt 3 * ‖x‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num : 0 < (2 : ENNReal).toReal)
    (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg x))
  norm_num only [ENNReal.toReal_ofNat]
  calc
    ∑' n, ‖ofHilbert x n‖ ^ (2 : ℝ) ≤
        ∑' n, (Real.sqrt 3 * ‖x n‖) ^ (2 : ℝ) := by
      apply Summable.tsum_le_tsum
      · intro n
        have h := BlockSpace.norm_le_sqrtThree_mul_hilbert_norm
          ((BlockSpace.linearEquivHilbert n).symm (x n))
        have h' : ‖(BlockSpace.linearEquivHilbert n).symm (x n)‖ ≤
            Real.sqrt 3 * ‖x n‖ := by
          simpa using h
        exact Real.rpow_le_rpow (norm_nonneg _) h' (by norm_num)
      · exact (lp.memℓp (ofHilbert x)).summable (by norm_num)
      · have hs : Summable (fun n ↦ ‖x n‖ ^ 2) := by
          simpa using (lp.memℓp x).summable
            (by norm_num : 0 < (2 : ENNReal).toReal)
        have hm := hs.mul_left ((Real.sqrt 3) ^ 2)
        simpa [Real.rpow_two, mul_pow] using hm
    _ = (Real.sqrt 3 * ‖x‖) ^ (2 : ℝ) := by
      have hs : Summable (fun n ↦ ‖x n‖ ^ 2) := by
        simpa using (lp.memℓp x).summable
          (by norm_num : 0 < (2 : ENNReal).toReal)
      calc
        ∑' n, (Real.sqrt 3 * ‖x n‖) ^ (2 : ℝ) =
            ∑' n, (Real.sqrt 3) ^ 2 * ‖x n‖ ^ 2 := by
          apply tsum_congr
          intro n
          rw [Real.rpow_two, mul_pow]
        _ = (Real.sqrt 3) ^ 2 * ∑' n, ‖x n‖ ^ 2 :=
          hs.tsum_mul_left ((Real.sqrt 3) ^ 2)
        _ = (Real.sqrt 3 * ‖x‖) ^ (2 : ℝ) := by
          have hxnorm : ‖x‖ ^ 2 = ∑' n, ‖x n‖ ^ 2 := by
            simpa [Real.rpow_two] using
              (lp.norm_rpow_eq_tsum
                (by norm_num : 0 < (2 : ENNReal).toReal) x)
          rw [← hxnorm]
          rw [Real.rpow_two]
          ring

/-- `XSpace` is continuously linearly equivalent to its Hilbert `ℓ₂` model,
with forward bound `1` and inverse bound `√3`. -/
noncomputable def continuousLinearEquivHilbertSum : XSpace ≃L[ℝ] XHilbertSpace :=
  linearEquivHilbertSum.toContinuousLinearEquivOfBounds 1 (Real.sqrt 3)
    (fun x ↦ by simpa using norm_toHilbert_le x)
    (fun x ↦ by simpa using norm_ofHilbert_le x)

end

end NormFormula.X
