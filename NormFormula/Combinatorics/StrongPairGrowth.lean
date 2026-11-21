import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Sqrt
import NormFormula.Combinatorics.ScaleSensitivePacking

/-!
# Numerical growth bounds for strong-pair packing

The exact combinatorial quantities are convenient for the recurrence proof,
but asymptotic use only needs two coarse estimates: the bounded-pair total is
polynomial for fixed range and dimension, and the iterated family threshold is
at most a fixed row-dependent base raised to the recurrence depth.
-/

namespace NormFormula

open Filter

/-- Coarse polynomial bound for the exact number of threshold pairs. -/
theorem strongShatteringPairBound_le_polynomial
    (rowCount levelCount dimension : ℕ) :
    strongShatteringPairBound rowCount levelCount dimension ≤
      (dimension + 1) * (rowCount * levelCount + 1) ^ dimension := by
  unfold strongShatteringPairBound
  calc
    (∑ k : Fin (dimension + 1),
        Nat.choose rowCount k * levelCount ^ (k : ℕ)) ≤
        ∑ _k : Fin (dimension + 1),
          (rowCount * levelCount + 1) ^ dimension := by
      apply Finset.sum_le_sum
      intro k _
      have hk : (k : ℕ) ≤ dimension :=
        Nat.lt_succ_iff.mp k.isLt
      calc
        Nat.choose rowCount k * levelCount ^ (k : ℕ) ≤
            rowCount ^ (k : ℕ) * levelCount ^ (k : ℕ) :=
          Nat.mul_le_mul_right _ (Nat.choose_le_pow rowCount k)
        _ = (rowCount * levelCount) ^ (k : ℕ) := by
          rw [mul_pow]
        _ ≤ (rowCount * levelCount + 1) ^ (k : ℕ) :=
          Nat.pow_le_pow_left (Nat.le_succ _) _
        _ ≤ (rowCount * levelCount + 1) ^ dimension :=
          pow_le_pow_right' (by omega) hk
    _ = (dimension + 1) *
        (rowCount * levelCount + 1) ^ dimension := by
      simp

/-- The recursive family-size threshold is bounded by twice the `steps`-th
power of the largest recurrence multiplier encountered. -/
theorem strongPairIterationFamilySize_le_pow
    (rowCount levelCount steps : ℕ) :
    strongPairIterationFamilySize rowCount levelCount steps ≤
      2 * (2 * (rowCount * levelCount * levelCount)) ^ steps := by
  induction steps generalizing rowCount with
  | zero => simp
  | succ steps ih =>
      let parentBase := 2 * (rowCount * levelCount * levelCount)
      let childBase := 2 * ((rowCount - 1) * levelCount * levelCount)
      have hbase : childBase ≤ parentBase := by
        dsimp [childBase, parentBase]
        gcongr
        exact Nat.sub_le rowCount 1
      have hpow : childBase ^ steps ≤ parentBase ^ steps :=
        Nat.pow_le_pow_left hbase _
      calc
        strongPairIterationFamilySize rowCount levelCount (steps + 1) =
            parentBase * strongPairIterationFamilySize
              (rowCount - 1) levelCount steps := by
          simp [strongPairIterationFamilySize_succ, parentBase]
          ring
        _ ≤ parentBase * (2 * childBase ^ steps) :=
          Nat.mul_le_mul_left parentBase (ih (rowCount - 1))
        _ ≤ parentBase * (2 * parentBase ^ steps) :=
          Nat.mul_le_mul_left parentBase
            (Nat.mul_le_mul_left 2 hpow)
        _ = 2 * parentBase ^ (steps + 1) := by
          rw [pow_succ]
          ring

/-- At square-root recurrence depth, the exponential lower count eventually
dominates the fixed-dimension polynomial total of threshold pairs. -/
theorem eventually_strongShatteringPairBound_lt_two_pow_sqrt
    (levelCount dimension : ℕ) :
    ∀ᶠ rowCount : ℕ in atTop,
      strongShatteringPairBound rowCount levelCount dimension <
        2 ^ Nat.sqrt rowCount := by
  let coefficient := (dimension + 1) * (levelCount + 1) ^ dimension
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.mp
    (eventually_polynomial_lt_two_pow coefficient (2 * dimension))
  filter_upwards [eventually_ge_atTop (threshold ^ 2)] with rowCount hrowCount
  let root := Nat.sqrt rowCount
  have hthresholdRoot : threshold ≤ root := by
    apply Nat.le_sqrt'.mpr
    exact hrowCount
  have hrootUpper : rowCount ≤ (root + 1) ^ 2 := by
    exact Nat.le_of_lt (Nat.lt_succ_sqrt' rowCount)
  have hsquarePos : 1 ≤ (root + 1) ^ 2 := by
    simpa using Nat.pow_le_pow_left
      (Nat.succ_le_succ (Nat.zero_le root)) 2
  have hbase : rowCount * levelCount + 1 ≤
      (levelCount + 1) * (root + 1) ^ 2 := by
    calc
      rowCount * levelCount + 1 ≤
          (root + 1) ^ 2 * levelCount + 1 := by
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_right levelCount hrootUpper) 1
      _ ≤ (root + 1) ^ 2 * levelCount + (root + 1) ^ 2 :=
        Nat.add_le_add_left hsquarePos _
      _ = (levelCount + 1) * (root + 1) ^ 2 := by ring
  have hpolynomial :
      (dimension + 1) * (rowCount * levelCount + 1) ^ dimension <
        2 ^ root := by
    calc
      (dimension + 1) * (rowCount * levelCount + 1) ^ dimension ≤
          (dimension + 1) *
            ((levelCount + 1) * (root + 1) ^ 2) ^ dimension :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase _)
      _ = coefficient * (root + 1) ^ (2 * dimension) := by
        dsimp [coefficient]
        rw [mul_pow, pow_mul]
        ring
      _ < 2 ^ root := hthreshold root hthresholdRoot
  exact (strongShatteringPairBound_le_polynomial
    rowCount levelCount dimension).trans_lt hpolynomial

/-- The recursive threshold at square-root depth is square-subexponential. -/
theorem eventually_sq_strongPairIterationFamilySize_sqrt_lt_two_pow
    (levelCount : ℕ) :
    ∀ᶠ rowCount : ℕ in atTop,
      (strongPairIterationFamilySize rowCount levelCount
        (Nat.sqrt rowCount)) ^ 2 < 2 ^ rowCount := by
  let coefficient := (4 * levelCount * levelCount) ^ 2
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.mp
    (eventually_polynomial_lt_two_pow coefficient 4)
  let start := max threshold 1
  filter_upwards [eventually_ge_atTop (start ^ 2)] with rowCount hrowCount
  let root := Nat.sqrt rowCount
  let recurrenceBase := 2 * (rowCount * levelCount * levelCount)
  have hstartRoot : start ≤ root := by
    apply Nat.le_sqrt'.mpr
    exact hrowCount
  have hthresholdRoot : threshold ≤ root :=
    (Nat.le_max_left _ _).trans hstartRoot
  have hrootPos : 0 < root := by
    have honeRoot : 1 ≤ root :=
      (Nat.le_max_right _ _).trans hstartRoot
    exact Nat.zero_lt_of_lt honeRoot
  have hrootUpper : rowCount ≤ (root + 1) ^ 2 := by
    exact Nat.le_of_lt (Nat.lt_succ_sqrt' rowCount)
  have htwiceBase : 2 * recurrenceBase ≤
      4 * (root + 1) ^ 2 * levelCount * levelCount := by
    dsimp [recurrenceBase]
    calc
      2 * (2 * (rowCount * levelCount * levelCount)) =
          4 * rowCount * levelCount * levelCount := by ring
      _ ≤ 4 * (root + 1) ^ 2 * levelCount * levelCount := by
        gcongr
  have hbaseSquare : (2 * recurrenceBase) ^ 2 < 2 ^ root := by
    calc
      (2 * recurrenceBase) ^ 2 ≤
          (4 * (root + 1) ^ 2 * levelCount * levelCount) ^ 2 :=
        Nat.pow_le_pow_left htwiceBase _
      _ = coefficient * (root + 1) ^ 4 := by
        dsimp [coefficient]
        ring
      _ < 2 ^ root := hthreshold root hthresholdRoot
  have hfour : 4 ≤ 4 ^ root := by
    have := pow_le_pow_right' (a := (4 : ℕ)) (by omega : 1 ≤ 4)
      (show 1 ≤ root from Nat.one_le_iff_ne_zero.mpr hrootPos.ne')
    simpa using this
  have hthresholdPower :
      (2 * recurrenceBase ^ root) ^ 2 ≤
        ((2 * recurrenceBase) ^ 2) ^ root := by
    calc
      (2 * recurrenceBase ^ root) ^ 2 =
          2 ^ 2 * (recurrenceBase ^ root) ^ 2 := by
        rw [mul_pow]
      _ = 4 * recurrenceBase ^ (root * 2) := by
        rw [← pow_mul]
        norm_num
      _ = 4 * recurrenceBase ^ (2 * root) := by
        rw [Nat.mul_comm root 2]
      _ ≤ 4 ^ root * recurrenceBase ^ (2 * root) :=
        Nat.mul_le_mul_right _ hfour
      _ = ((2 * recurrenceBase) ^ 2) ^ root := by
        symm
        calc
          ((2 * recurrenceBase) ^ 2) ^ root =
              (2 * recurrenceBase) ^ (2 * root) := by
            rw [← pow_mul]
          _ = 2 ^ (2 * root) * recurrenceBase ^ (2 * root) := by
            rw [mul_pow]
          _ = 4 ^ root * recurrenceBase ^ (2 * root) := by
            rw [pow_mul]
            norm_num
  calc
    (strongPairIterationFamilySize rowCount levelCount root) ^ 2 ≤
        (2 * recurrenceBase ^ root) ^ 2 :=
      Nat.pow_le_pow_left
        (strongPairIterationFamilySize_le_pow rowCount levelCount root) _
    _ ≤ ((2 * recurrenceBase) ^ 2) ^ root := hthresholdPower
    _ < (2 ^ root) ^ root :=
      Nat.pow_lt_pow_left hbaseSquare hrootPos.ne'
    _ = 2 ^ (root * root) := by rw [pow_mul]
    _ ≤ 2 ^ rowCount :=
      Nat.pow_le_pow_right (by omega) (Nat.sqrt_le rowCount)

end NormFormula
