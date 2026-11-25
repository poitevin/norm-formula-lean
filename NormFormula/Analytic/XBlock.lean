import NormFormula.Analytic.AugmentedNorm
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The finite-dimensional cube blocks for `X`

For `n : ℕ`, the paper uses a Hilbert space with orthonormal basis indexed by
the rows `i : Fin n` and the subsets `S : Finset (Fin n)`.  This file realizes
that space as a finite Euclidean coordinate space, defines

`M_n(z) = max_{i ∈ S} (|z(f_i)| + |z(e_S)|)`,

and verifies the uniform Hilbert comparison and the exact cube values of the
augmented norm `N_n`.
-/

namespace NormFormula.X

/-- The coordinates corresponding respectively to `f_i` and `e_S`. -/
abbrev BlockIndex (n : ℕ) := Fin n ⊕ Finset (Fin n)

/-- The finite-dimensional Hilbert space `H_n`. -/
abbrev BlockHilbert (n : ℕ) := EuclideanSpace ℝ (BlockIndex n)

/-- An admissible pair `(i,S)` with `i ∈ S`. -/
abbrev BlockPair (n : ℕ) := {p : Fin n × Finset (Fin n) // p.1 ∈ p.2}

/-- The row basis vector `f_i`. -/
noncomputable def rowVector {n : ℕ} (i : Fin n) : BlockHilbert n :=
  EuclideanSpace.single (Sum.inl i) 1

/-- The subset basis vector `e_S`. -/
noncomputable def subsetVector {n : ℕ} (S : Finset (Fin n)) : BlockHilbert n :=
  EuclideanSpace.single (Sum.inr S) 1

@[simp]
theorem rowVector_apply_inl {n : ℕ} (i j : Fin n) :
    rowVector i (Sum.inl j) = if j = i then 1 else 0 := by
  simp [rowVector, PiLp.single_apply]

@[simp]
theorem rowVector_apply_inr {n : ℕ} (i : Fin n) (S : Finset (Fin n)) :
    rowVector i (Sum.inr S) = 0 := by
  simp [rowVector]

@[simp]
theorem subsetVector_apply_inl {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    subsetVector S (Sum.inl i) = 0 := by
  simp [subsetVector]

@[simp]
theorem subsetVector_apply_inr {n : ℕ}
    (S T : Finset (Fin n)) :
    subsetVector S (Sum.inr T) = if T = S then 1 else 0 := by
  simp [subsetVector, PiLp.single_apply]

/-- The summand `|z(f_i)| + |z(e_S)|` as a Mathlib seminorm. -/
noncomputable def pairSeminorm {n : ℕ} (i : Fin n)
    (S : Finset (Fin n)) : Seminorm ℝ (BlockHilbert n) :=
  Seminorm.of
    (fun z ↦ |z (Sum.inl i)| + |z (Sum.inr S)|)
    (fun x y ↦ by
      simp only [PiLp.add_apply]
      calc
        |x (Sum.inl i) + y (Sum.inl i)| +
            |x (Sum.inr S) + y (Sum.inr S)| ≤
            (|x (Sum.inl i)| + |y (Sum.inl i)|) +
              (|x (Sum.inr S)| + |y (Sum.inr S)|) :=
          add_le_add (abs_add_le _ _) (abs_add_le _ _)
        _ = (|x (Sum.inl i)| + |x (Sum.inr S)|) +
              (|y (Sum.inl i)| + |y (Sum.inr S)|) := by ring)
    (fun r x ↦ by
      simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, Real.norm_eq_abs]
      ring)

@[simp]
theorem pairSeminorm_apply {n : ℕ} (i : Fin n)
    (S : Finset (Fin n)) (z : BlockHilbert n) :
    pairSeminorm i S z = |z (Sum.inl i)| + |z (Sum.inr S)| :=
  rfl

/-- Each admissible summand is at most `sqrt 2` times the Hilbert norm. -/
theorem pairSeminorm_le_sqrtTwo_mul_norm {n : ℕ} (i : Fin n)
    (S : Finset (Fin n)) (z : BlockHilbert n) :
    pairSeminorm i S z ≤ Real.sqrt 2 * ‖z‖ := by
  have hcoords :
      z (Sum.inl i) ^ 2 + z (Sum.inr S) ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      z (Sum.inl i) ^ 2 + z (Sum.inr S) ^ 2 =
          ∑ c ∈ ({Sum.inl i, Sum.inr S} : Finset (BlockIndex n)),
            z c ^ 2 := by simp
      _ ≤ ∑ c : BlockIndex n, z c ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro c _ _
        exact sq_nonneg (z c)
  have hsquare :
      (|z (Sum.inl i)| + |z (Sum.inr S)|) ^ 2 ≤ 2 * ‖z‖ ^ 2 := by
    nlinarith [sq_abs (z (Sum.inl i)), sq_abs (z (Sum.inr S)),
      sq_nonneg (|z (Sum.inl i)| - |z (Sum.inr S)|)]
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 * ‖z‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hsqrt_sq : (Real.sqrt 2 * ‖z‖) ^ 2 = 2 * ‖z‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  rw [pairSeminorm_apply]
  nlinarith [abs_nonneg (z (Sum.inl i)), abs_nonneg (z (Sum.inr S))]

/-- The maximum of the admissible pair seminorms.  For `n = 0` the indexing
set is empty and this is the zero seminorm. -/
noncomputable def blockSeminorm (n : ℕ) : Seminorm ℝ (BlockHilbert n) :=
  Finset.univ.sup fun p : BlockPair n ↦ pairSeminorm p.1.1 p.1.2

/-- Every admissible pair is bounded by the block seminorm. -/
theorem pairSeminorm_le_blockSeminorm {n : ℕ} (p : BlockPair n)
    (z : BlockHilbert n) :
    pairSeminorm p.1.1 p.1.2 z ≤ blockSeminorm n z := by
  change pairSeminorm p.1.1 p.1.2 z ≤
    (Finset.univ.sup fun q : BlockPair n ↦ pairSeminorm q.1.1 q.1.2) z
  exact Seminorm.le_finset_sup_apply
    (p := fun q : BlockPair n ↦ pairSeminorm q.1.1 q.1.2)
    (s := Finset.univ) (x := z) (i := p) (Finset.mem_univ p)

/-- The block maximum retains the common sharp `sqrt 2` bound. -/
theorem blockSeminorm_le_sqrtTwo_mul_norm {n : ℕ} (z : BlockHilbert n) :
    blockSeminorm n z ≤ Real.sqrt 2 * ‖z‖ := by
  apply Seminorm.finset_sup_apply_le
  · positivity
  · intro p _
    exact pairSeminorm_le_sqrtTwo_mul_norm p.1.1 p.1.2 z

/-- Squared form of the uniform bound. -/
theorem blockSeminorm_sq_le_two_mul_norm_sq {n : ℕ} (z : BlockHilbert n) :
    blockSeminorm n z ^ 2 ≤ 2 * ‖z‖ ^ 2 := by
  have h := blockSeminorm_le_sqrtTwo_mul_norm z
  have hsqrt_sq : (Real.sqrt 2 * ‖z‖) ^ 2 = 2 * ‖z‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  nlinarith [apply_nonneg (blockSeminorm n) z,
    Real.sqrt_nonneg (2 : ℝ), norm_nonneg z]

/-- The paper's augmented norm `N_n`. -/
noncomputable def blockNorm {n : ℕ} (z : BlockHilbert n) : ℝ :=
  augmentedNorm (blockSeminorm n) z

/-- The Hilbert norm is below `N_n`. -/
theorem norm_le_blockNorm {n : ℕ} (z : BlockHilbert n) :
    ‖z‖ ≤ blockNorm z :=
  norm_le_augmentedNorm (blockSeminorm n) z

/-- Uniform upper comparison `N_n(z) ≤ sqrt 3 * ‖z‖`. -/
theorem blockNorm_le_sqrtThree_mul_norm {n : ℕ} (z : BlockHilbert n) :
    blockNorm z ≤ Real.sqrt 3 * ‖z‖ :=
  augmentedNorm_le_sqrtThree_mul (blockSeminorm n)
    blockSeminorm_sq_le_two_mul_norm_sq z

@[simp]
theorem rowVector_norm {n : ℕ} (i : Fin n) : ‖rowVector i‖ = 1 := by
  simp [rowVector, PiLp.norm_single]

@[simp]
theorem subsetVector_norm {n : ℕ} (S : Finset (Fin n)) :
    ‖subsetVector S‖ = 1 := by
  simp [subsetVector, PiLp.norm_single]

/-- The two different basis coordinates have Hilbert norm squared equal to
`2`. -/
theorem norm_sq_row_add_subset {n : ℕ} (i : Fin n)
    (S : Finset (Fin n)) :
    ‖rowVector i + subsetVector S‖ ^ 2 = 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [rowVector, subsetVector, PiLp.single_apply]
  norm_num

/-- The block seminorm of a row basis vector is exactly `1`. -/
@[simp]
theorem blockSeminorm_rowVector {n : ℕ} (i : Fin n) :
    blockSeminorm n (rowVector i) = 1 := by
  apply le_antisymm
  · apply Seminorm.finset_sup_apply_le (by norm_num)
    intro p _
    rw [pairSeminorm_apply]
    by_cases hpi : p.1.1 = i
    · simp [hpi]
    · simp [hpi]
  · let p : BlockPair n :=
      ⟨(i, {i}), Finset.mem_singleton_self i⟩
    calc
      (1 : ℝ) = pairSeminorm i {i} (rowVector i) := by
        rw [pairSeminorm_apply]
        simp
      _ ≤ blockSeminorm n (rowVector i) := by
        simpa [p] using pairSeminorm_le_blockSeminorm p (rowVector i)

/-- Every subset basis vector has block seminorm at most `1` (the empty
subset has value `0`). -/
theorem blockSeminorm_subsetVector_le_one {n : ℕ}
    (S : Finset (Fin n)) :
    blockSeminorm n (subsetVector S) ≤ 1 := by
  apply Seminorm.finset_sup_apply_le (by norm_num)
  intro p _
  rw [pairSeminorm_apply]
  by_cases hpS : p.1.2 = S
  · simp [hpS]
  · simp [hpS]

/-- The rows lie on the `sqrt 2` sphere for the augmented block norm. -/
@[simp]
theorem blockNorm_rowVector {n : ℕ} (i : Fin n) :
    blockNorm (rowVector i) = Real.sqrt 2 := by
  rw [blockNorm, augmentedNorm, rowVector_norm, blockSeminorm_rowVector]
  norm_num

/-- All subset parameters lie in the fixed `sqrt 2` ball for the augmented
block norm. -/
theorem blockNorm_subsetVector_le_sqrtTwo {n : ℕ}
    (S : Finset (Fin n)) :
    blockNorm (subsetVector S) ≤ Real.sqrt 2 := by
  have hM := blockSeminorm_subsetVector_le_one S
  have hMnonneg := apply_nonneg (blockSeminorm n) (subsetVector S)
  rw [blockNorm, augmentedNorm, subsetVector_norm, Real.sqrt_le_iff]
  constructor
  · exact Real.sqrt_nonneg _
  · rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
    nlinarith

/-- If `i ∈ S`, the admissible pair `(i,S)` sees both unit coordinates. -/
theorem blockSeminorm_row_add_subset_of_mem {n : ℕ} (i : Fin n)
    (S : Finset (Fin n)) (hi : i ∈ S) :
    blockSeminorm n (rowVector i + subsetVector S) = 2 := by
  apply le_antisymm
  · have hnorm : ‖rowVector i + subsetVector S‖ = Real.sqrt 2 := by
      have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith [norm_sq_row_add_subset i S, norm_nonneg (rowVector i + subsetVector S),
        Real.sqrt_nonneg (2 : ℝ)]
    have h := blockSeminorm_le_sqrtTwo_mul_norm
      (rowVector i + subsetVector S)
    rw [hnorm] at h
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · let p : BlockPair n := ⟨(i, S), hi⟩
    calc
      (2 : ℝ) = pairSeminorm i S (rowVector i + subsetVector S) := by
        rw [pairSeminorm_apply]
        simp
        norm_num
      _ ≤ blockSeminorm n (rowVector i + subsetVector S) := by
        simpa [p] using pairSeminorm_le_blockSeminorm p
          (rowVector i + subsetVector S)

/-- If `i ∉ S`, no admissible pair sees both unit coordinates. -/
theorem blockSeminorm_row_add_subset_of_not_mem {n : ℕ} (i : Fin n)
    (S : Finset (Fin n)) (hi : i ∉ S) :
    blockSeminorm n (rowVector i + subsetVector S) = 1 := by
  apply le_antisymm
  · apply Seminorm.finset_sup_apply_le (by norm_num)
    intro p _
    by_cases hpi : p.1.1 = i
    · by_cases hpS : p.1.2 = S
      · exfalso
        apply hi
        simpa [hpi, hpS] using p.2
      · rw [pairSeminorm_apply]
        simp [hpi, hpS]
    · by_cases hpS : p.1.2 = S
      · rw [pairSeminorm_apply]
        simp [hpi, hpS]
      · rw [pairSeminorm_apply]
        simp [hpi, hpS]
  · let p : BlockPair n :=
      ⟨(i, {i}), Finset.mem_singleton_self i⟩
    have hS : S ≠ {i} := by
      intro h
      apply hi
      rw [h]
      exact Finset.mem_singleton_self i
    have hS' : ({i} : Finset (Fin n)) ≠ S := Ne.symm hS
    calc
      (1 : ℝ) = pairSeminorm i {i} (rowVector i + subsetVector S) := by
        rw [pairSeminorm_apply]
        simp [hS']
      _ ≤ blockSeminorm n (rowVector i + subsetVector S) := by
        simpa [p] using pairSeminorm_le_blockSeminorm p
          (rowVector i + subsetVector S)


/-- Exact high cube value. -/
theorem blockNorm_row_add_subset_of_mem {n : ℕ} (i : Fin n)
    (S : Finset (Fin n)) (hi : i ∈ S) :
    blockNorm (rowVector i + subsetVector S) = Real.sqrt 6 := by
  rw [blockNorm, augmentedNorm, norm_sq_row_add_subset,
    blockSeminorm_row_add_subset_of_mem i S hi]
  norm_num

/-- Exact low cube value. -/
theorem blockNorm_row_add_subset_of_not_mem {n : ℕ} (i : Fin n)
    (S : Finset (Fin n)) (hi : i ∉ S) :
    blockNorm (rowVector i + subsetVector S) = Real.sqrt 3 := by
  rw [blockNorm, augmentedNorm, norm_sq_row_add_subset,
    blockSeminorm_row_add_subset_of_not_mem i S hi]
  norm_num

/-- The exact finite cube pattern in one statement. -/
theorem blockNorm_row_add_subset {n : ℕ} (i : Fin n)
    (S : Finset (Fin n)) :
    blockNorm (rowVector i + subsetVector S) =
      if i ∈ S then Real.sqrt 6 else Real.sqrt 3 := by
  split_ifs with hi
  · exact blockNorm_row_add_subset_of_mem i S hi
  · exact blockNorm_row_add_subset_of_not_mem i S hi

end NormFormula.X
