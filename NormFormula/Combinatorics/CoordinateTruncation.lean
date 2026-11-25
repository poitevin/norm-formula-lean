import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Set.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import NormFormula.Analytic.HalfGraphSeminorm

/-!
# Coordinate truncation in `ℓ₂`

At a fixed positive threshold, a square-summable sequence has only finitely
many coordinates above that threshold.  We prove the quantitative cardinality
bound used in the paper, first for one copy of `ℓ₂(ℕ)` and then for the
Hilbertian product of two copies.
-/

namespace NormFormula.HalfGraph

open scoped ENNReal

/-- The coordinates of `u` whose absolute value is at least `η`. -/
def largeCoordinates (u : RealL2) (η : ℝ) : Set ℕ :=
  {i | η ≤ |u i|}

/-- A square-summable sequence has only finitely many coordinates above a
fixed positive threshold. -/
theorem largeCoordinates_finite (u : RealL2) {η : ℝ} (hη : 0 < η) :
    (largeCoordinates u η).Finite := by
  have hsummable : Summable (fun i : ℕ ↦ (u i) ^ 2) := by
    simpa [Real.norm_eq_abs, sq_abs] using
      (lp.memℓp u).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hfinite : Set.Finite {i : ℕ | η ^ 2 ≤ (u i) ^ 2} := by
    simpa using
      hsummable.tendsto_cofinite_zero.eventually_lt_const (sq_pos_of_pos hη)
  refine hfinite.subset fun i hi ↦ ?_
  simpa [sq_abs] using (sq_le_sq₀ hη.le (abs_nonneg (u i))).2 hi

/-- Quantitative form of coordinate truncation for one copy of `ℓ₂`: the
number of retained coordinates times `η²` is at most the squared norm. -/
theorem largeCoordinates_ncard_mul_sq_le_norm_sq (u : RealL2) {η : ℝ} (hη : 0 < η) :
    ((largeCoordinates u η).ncard : ℝ) * η ^ 2 ≤ ‖u‖ ^ 2 := by
  let hfinite := largeCoordinates_finite u hη
  let s := hfinite.toFinset
  have hlower : (s.card : ℝ) * η ^ 2 ≤ ∑ i ∈ s, (u i) ^ 2 := by
    simpa [nsmul_eq_mul] using
      Finset.card_nsmul_le_sum s (fun i ↦ (u i) ^ 2) (η ^ 2) (fun i hi ↦ by
        have hi' : i ∈ largeCoordinates u η := hfinite.mem_toFinset.mp hi
        simpa [sq_abs] using (sq_le_sq₀ hη.le (abs_nonneg (u i))).2 hi')
  have hupper : ∑ i ∈ s, (u i) ^ 2 ≤ ‖u‖ ^ 2 := by
    simpa [Real.norm_eq_abs, sq_abs] using
      lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal) u s
  calc
    ((largeCoordinates u η).ncard : ℝ) * η ^ 2 = (s.card : ℝ) * η ^ 2 := by
      rw [Set.ncard_eq_toFinset_card _ hfinite]
    _ ≤ ‖u‖ ^ 2 := hlower.trans hupper


/-- The number of coordinates retained across both copies of `ℓ₂`. -/
noncomputable def pairLargeCoordinateCount (z : HilbertSpace) (η : ℝ) : ℕ :=
  (largeCoordinates z.fst η).ncard + (largeCoordinates z.snd η).ncard

/-- Quantitative coordinate-truncation bound for the Hilbertian product. -/
theorem pairLargeCoordinateCount_mul_sq_le_norm_sq (z : HilbertSpace) {η : ℝ}
    (hη : 0 < η) :
    (pairLargeCoordinateCount z η : ℝ) * η ^ 2 ≤ ‖z‖ ^ 2 := by
  rw [pairLargeCoordinateCount, Nat.cast_add, add_mul, WithLp.prod_norm_sq_eq_of_L2]
  exact add_le_add
    (largeCoordinates_ncard_mul_sq_le_norm_sq z.fst hη)
    (largeCoordinates_ncard_mul_sq_le_norm_sq z.snd hη)

/-- The paper's support estimate: truncating both copies at threshold `η`
retains at most `⌊C² / η²⌋` coordinates in total on the ball of radius `C`. -/
theorem pairLargeCoordinateCount_le_floor (z : HilbertSpace) {C η : ℝ}
    (hz : ‖z‖ ≤ C) (hη : 0 < η) :
    pairLargeCoordinateCount z η ≤ ⌊C ^ 2 / η ^ 2⌋₊ := by
  have hC : 0 ≤ C := (norm_nonneg z).trans hz
  rw [Nat.le_floor_iff (div_nonneg (sq_nonneg C) (sq_nonneg η))]
  apply (le_div_iff₀ (sq_pos_of_pos hη)).2
  exact (pairLargeCoordinateCount_mul_sq_le_norm_sq z hη).trans
    ((sq_le_sq₀ (norm_nonneg z) hC).2 hz)

end NormFormula.HalfGraph
