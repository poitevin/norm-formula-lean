import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import NormFormula.Combinatorics.CoordinateTruncation

/-!
# Sparse coordinate truncation and approximation of `q`

We define the paper's truncation operator `Tη`, which retains precisely the
coordinates whose absolute value is at least `η`.  Its support is controlled by
the coordinate-counting results in `CoordinateTruncation`, and truncating both
arguments changes the ordered-pair seminorm by at most `4η`.
-/

namespace NormFormula.HalfGraph

open scoped ENNReal

/-- Retain the coordinates of `u` whose absolute value is at least `η`. -/
noncomputable def truncateSequence (u : RealL2) (η : ℝ) : RealL2 :=
  ⟨fun i ↦ if η ≤ |u i| then u i else 0, by
    apply memℓp_gen
    refine Summable.of_nonneg_of_le (fun i ↦ by positivity) (fun i ↦ ?_)
      ((lp.memℓp u).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))
    by_cases hi : η ≤ |u i|
    · simp [hi]
    · simpa [hi] using sq_nonneg (u i)⟩

@[simp]
theorem truncateSequence_apply (u : RealL2) (η : ℝ) (i : ℕ) :
    truncateSequence u η i = if η ≤ |u i| then u i else 0 := rfl

/-- At positive threshold, the support of the truncated sequence is exactly
the set of retained coordinates. -/
theorem support_truncateSequence (u : RealL2) {η : ℝ} (hη : 0 < η) :
    Function.support (truncateSequence u η) = largeCoordinates u η := by
  ext i
  by_cases hi : η ≤ |u i|
  · have hui : u i ≠ 0 := abs_pos.mp (hη.trans_le hi)
    simp [Function.mem_support, truncateSequence_apply, largeCoordinates, hi, hui]
  · simp [Function.mem_support, truncateSequence_apply, largeCoordinates, hi]

/-- Every discarded coordinate has absolute value strictly below the
truncation threshold. -/
theorem abs_sub_truncateSequence_lt (u : RealL2) {η : ℝ} (hη : 0 < η) (i : ℕ) :
    |u i - truncateSequence u η i| < η := by
  rw [truncateSequence_apply]
  by_cases hi : η ≤ |u i|
  · simp [hi, hη]
  · simpa [hi] using lt_of_not_ge hi

/-- Coordinate truncation on both copies of `ℓ₂`. -/
noncomputable def truncate (z : HilbertSpace) (η : ℝ) : HilbertSpace :=
  WithLp.toLp 2 (truncateSequence z.fst η, truncateSequence z.snd η)

@[simp]
theorem truncate_fst (z : HilbertSpace) (η : ℝ) :
    (truncate z η).fst = truncateSequence z.fst η := rfl

@[simp]
theorem truncate_snd (z : HilbertSpace) (η : ℝ) :
    (truncate z η).snd = truncateSequence z.snd η := rfl

/-- The support of `Tη z`, counting both copies, is the large-coordinate
count defined in the preceding module. -/
theorem truncate_support_count (z : HilbertSpace) {η : ℝ} (hη : 0 < η) :
    (Function.support (truncate z η).fst).ncard +
        (Function.support (truncate z η).snd).ncard =
      pairLargeCoordinateCount z η := by
  rw [truncate_fst, truncate_snd, support_truncateSequence z.fst hη,
    support_truncateSequence z.snd hη, pairLargeCoordinateCount]

/-- The exact support bound for the truncation operator on a Hilbert ball. -/
theorem truncate_support_count_le_floor (z : HilbertSpace) {C η : ℝ}
    (hz : ‖z‖ ≤ C) (hη : 0 < η) :
    (Function.support (truncate z η).fst).ncard +
        (Function.support (truncate z η).snd).ncard ≤
      ⌊C ^ 2 / η ^ 2⌋₊ := by
  rw [truncate_support_count z hη]
  exact pairLargeCoordinateCount_le_floor z hz hη

/-- Coordinatewise bounds on the two copies control the change in `q`. -/
theorem abs_qSeminorm_sub_le_of_coordinate_bounds {z w : HilbertSpace} {a b : ℝ}
    (hfst : ∀ i, |z.fst i - w.fst i| ≤ a)
    (hsnd : ∀ j, |z.snd j - w.snd j| ≤ b) :
    |qSeminorm z - qSeminorm w| ≤ a + b := by
  have hqdiff : qSeminorm (z - w) ≤ a + b := by
    rw [qSeminorm_apply]
    refine ciSup_le fun p ↦ ?_
    change |(z.fst p.1.1 - w.fst p.1.1) + (z.snd p.1.2 - w.snd p.1.2)| ≤ a + b
    exact (abs_add_le _ _).trans (add_le_add (hfst p.1.1) (hsnd p.1.2))
  have hseminorm := Seminorm.norm_sub_map_le_sub qSeminorm z w
  simpa [Real.norm_eq_abs] using hseminorm.trans hqdiff

/-- Truncating both summands changes `q` by at most `4η`, as in
Equation (q-truncation) of the paper. -/
theorem abs_qSeminorm_add_sub_truncate_le (x y : HilbertSpace) {η : ℝ} (hη : 0 < η) :
    |qSeminorm (x + y) - qSeminorm (truncate x η + truncate y η)| ≤ 4 * η := by
  have hcoordinate (u v : RealL2) (i : ℕ) :
      |(u i + v i) - (truncateSequence u η i + truncateSequence v η i)| ≤ 2 * η := by
    calc
      _ = |(u i - truncateSequence u η i) + (v i - truncateSequence v η i)| := by ring_nf
      _ ≤ |u i - truncateSequence u η i| + |v i - truncateSequence v η i| := abs_add_le _ _
      _ ≤ η + η := add_le_add (abs_sub_truncateSequence_lt u hη i).le
        (abs_sub_truncateSequence_lt v hη i).le
      _ = 2 * η := by ring
  have hq := abs_qSeminorm_sub_le_of_coordinate_bounds
    (z := x + y) (w := truncate x η + truncate y η)
    (hcoordinate x.fst y.fst) (hcoordinate x.snd y.snd)
  linarith

end NormFormula.HalfGraph
