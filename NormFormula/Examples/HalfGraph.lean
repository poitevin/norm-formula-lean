import NormFormula.Analytic.YSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The exact half-graph in the renormed Hilbert space

For the standard basis vectors `x_i = (e_i, 0)` and `y_j = (0, e_j)`, this
file computes the ordered-pair seminorm and the resulting `Y`-norm exactly.
-/

namespace NormFormula.HalfGraph

open scoped ENNReal

/-- The `i`th standard unit vector in real `ℓ₂(ℕ)`. -/
noncomputable def basisVector (i : ℕ) : RealL2 :=
  lp.single 2 i 1

@[simp]
theorem basisVector_apply (i k : ℕ) :
    basisVector i k = if i = k then 1 else 0 := by
  by_cases hik : i = k
  · subst k
    simp [basisVector, lp.single_apply]
  · have hki : k ≠ i := Ne.symm hik
    simp [basisVector, lp.single_apply, hik, hki]

@[simp]
theorem basisVector_norm (i : ℕ) : ‖basisVector i‖ = 1 := by
  simp [basisVector, lp.norm_single]

/-- The basis vector in the first copy of `ℓ₂`. -/
noncomputable def xVector (i : ℕ) : HilbertSpace :=
  WithLp.toLp 2 (basisVector i, 0)

/-- The basis vector in the second copy of `ℓ₂`. -/
noncomputable def yVector (j : ℕ) : HilbertSpace :=
  WithLp.toLp 2 (0, basisVector j)

@[simp] theorem xVector_fst (i : ℕ) : (xVector i).fst = basisVector i := rfl
@[simp] theorem xVector_snd (i : ℕ) : (xVector i).snd = 0 := rfl
@[simp] theorem yVector_fst (j : ℕ) : (yVector j).fst = 0 := rfl
@[simp] theorem yVector_snd (j : ℕ) : (yVector j).snd = basisVector j := rfl

/-- The first second-copy basis vector is invisible to `q`: no index precedes `0`.
This is `q(0, e₁) = 0` in the paper's positive indexing. -/
theorem qSeminorm_yVector_zero : qSeminorm (yVector 0) = 0 := by
  rw [qSeminorm_apply]
  have h (p : OrderedPair) : |(yVector 0).fst p.1.1 + (yVector 0).snd p.1.2| = 0 := by
    rw [yVector_fst, yVector_snd, basisVector_apply, if_neg (Nat.zero_lt_of_lt p.2).ne]
    change |(0 : ℝ) + 0| = 0
    simp
  simp only [h, ciSup_const]

/-- Every individual admissible coordinate seminorm lies below `q`. -/
theorem pairSeminorm_le_qSeminorm (p : OrderedPair) (z : HilbertSpace) :
    pairSeminorm p.1.1 p.1.2 z ≤ qSeminorm z := by
  change orderedPairSeminorm p z ≤ qSeminorm z
  rw [qSeminorm]
  exact (le_ciSup (f := orderedPairSeminorm) orderedPairSeminorm_bddAbove p) z

/-- If `i < j`, the admissible pair `(i,j)` sees both nonzero coordinates. -/
theorem qSeminorm_x_add_y_of_lt {i j : ℕ} (hij : i < j) :
    qSeminorm (xVector i + yVector j) = 2 := by
  apply le_antisymm
  · rw [qSeminorm_apply]
    refine ciSup_le fun p => ?_
    simp only [WithLp.add_fst, WithLp.add_snd, xVector_fst, yVector_fst,
      xVector_snd, yVector_snd, zero_add, add_zero, basisVector_apply]
    split_ifs <;> norm_num
  · let p : OrderedPair := ⟨(i, j), hij⟩
    have hp := pairSeminorm_le_qSeminorm p (xVector i + yVector j)
    norm_num [p] at hp
    exact hp

/-- If `j ≤ i`, no admissible pair sees both nonzero coordinates. -/
theorem qSeminorm_x_add_y_of_ge {i j : ℕ} (hji : j ≤ i) :
    qSeminorm (xVector i + yVector j) = 1 := by
  apply le_antisymm
  · rw [qSeminorm_apply]
    refine ciSup_le fun p => ?_
    simp only [WithLp.add_fst, WithLp.add_snd, xVector_fst, yVector_fst,
      xVector_snd, yVector_snd, zero_add, add_zero, basisVector_apply]
    by_cases hai : i = p.1.1
    · by_cases hjb : j = p.1.2
      · exfalso
        omega
      · simp [hai, hjb]
    · by_cases hjb : j = p.1.2 <;> simp [hai, hjb]
  · let p : OrderedPair := ⟨(i, i + 1), Nat.lt_succ_self i⟩
    have hp := pairSeminorm_le_qSeminorm p (xVector i + yVector j)
    have hne : j ≠ i + 1 := by omega
    simpa [p, hne] using hp

/-- The underlying Hilbert norm of every `x_i + y_j` has square `2`. -/
theorem norm_sq_x_add_y (i j : ℕ) : ‖xVector i + yVector j‖ ^ 2 = 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp
  norm_num

/-- Exact `Y`-norm value on the upper half of the half-graph. -/
theorem yNorm_x_add_y_of_lt {i j : ℕ} (hij : i < j) :
    yNorm (xVector i + yVector j) = Real.sqrt 6 := by
  rw [yNorm, augmentedNorm]
  rw [norm_sq_x_add_y, qSeminorm_x_add_y_of_lt hij]
  norm_num

/-- Exact `Y`-norm value on the lower half of the half-graph. -/
theorem yNorm_x_add_y_of_ge {i j : ℕ} (hji : j ≤ i) :
    yNorm (xVector i + yVector j) = Real.sqrt 3 := by
  rw [yNorm, augmentedNorm]
  rw [norm_sq_x_add_y, qSeminorm_x_add_y_of_ge hji]
  norm_num

/-- The two values occurring in the half-graph are genuinely distinct. -/
theorem sqrtThree_lt_sqrtSix : Real.sqrt 3 < Real.sqrt 6 := by
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- The complete half-graph computation in a single statement. -/
theorem yNorm_x_add_y (i j : ℕ) :
    yNorm (xVector i + yVector j) =
      if i < j then Real.sqrt 6 else Real.sqrt 3 := by
  split_ifs with hij
  · exact yNorm_x_add_y_of_lt hij
  · exact yNorm_x_add_y_of_ge (Nat.le_of_not_gt hij)

/-- The first-coordinate basis sequence, now regarded as a sequence in the normed space `Y`. -/
noncomputable def xInY (i : ℕ) : Y := ⟨xVector i⟩

/-- The second-coordinate basis sequence, now regarded as a sequence in the normed space `Y`. -/
noncomputable def yInY (j : ℕ) : Y := ⟨yVector j⟩

@[simp]
theorem xInY_toHilbert (i : ℕ) : (xInY i).toHilbert = xVector i := rfl

@[simp]
theorem yInY_toHilbert (j : ℕ) : (yInY j).toHilbert = yVector j := rfl

/-- The half-graph stated using the ordinary norm of the actual normed space `Y`. -/
theorem norm_xInY_add_yInY (i j : ℕ) :
    ‖xInY i + yInY j‖ = if i < j then Real.sqrt 6 else Real.sqrt 3 := by
  change yNorm (xVector i + yVector j) = if i < j then Real.sqrt 6 else Real.sqrt 3
  exact yNorm_x_add_y i j

end NormFormula.HalfGraph
