import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.UniformSpace.UniformEmbedding
import NormFormula.Analytic.XBlock

/-!
# The renormed blocks and their `ℓ₂`-sum `X`

This file equips each Euclidean cube block `H_n` with the augmented norm `N_n`
as its actual Mathlib norm.  The resulting complete finite-dimensional spaces
are then assembled using Mathlib's dependent `lp` construction.  Finally, the
finite cube patterns are embedded into individual summands of the resulting
space `X`.
-/

namespace NormFormula.X

noncomputable section

/-- The `n`th Hilbert block equipped with the paper's augmented norm `N_n`. -/
structure BlockSpace (n : ℕ) where
  toHilbert : BlockHilbert n

namespace BlockSpace

/-- Forget the augmented norm and return to the Euclidean block. -/
def equivHilbert (n : ℕ) : BlockSpace n ≃ BlockHilbert n where
  toFun := toHilbert
  invFun := BlockSpace.mk
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (n : ℕ) : AddCommGroup (BlockSpace n) :=
  (equivHilbert n).addCommGroup

noncomputable instance (n : ℕ) : Module ℝ (BlockSpace n) :=
  (equivHilbert n).module ℝ

noncomputable instance (n : ℕ) : Norm (BlockSpace n) where
  norm z := blockNorm z.toHilbert

@[simp]
theorem norm_def {n : ℕ} (z : BlockSpace n) :
    ‖z‖ = blockNorm z.toHilbert :=
  rfl

@[ext]
theorem ext {n : ℕ} {x y : BlockSpace n}
    (h : x.toHilbert = y.toHilbert) : x = y := by
  cases x
  cases y
  simp_all

@[simp]
theorem toHilbert_zero {n : ℕ} : (0 : BlockSpace n).toHilbert = 0 :=
  rfl

@[simp]
theorem toHilbert_add {n : ℕ} (x y : BlockSpace n) :
    (x + y).toHilbert = x.toHilbert + y.toHilbert :=
  rfl

@[simp]
theorem toHilbert_neg {n : ℕ} (x : BlockSpace n) :
    (-x).toHilbert = -x.toHilbert :=
  rfl

@[simp]
theorem toHilbert_smul {n : ℕ} (r : ℝ) (x : BlockSpace n) :
    (r • x).toHilbert = r • x.toHilbert :=
  rfl

/-- The augmented-norm axioms on one block. -/
private noncomputable def normedSpaceCore (n : ℕ) :
    NormedSpace.Core ℝ (BlockSpace n) where
  norm_nonneg z := augmentedNorm_nonneg (blockSeminorm n) z.toHilbert
  norm_smul r z := by
    change blockNorm (r • z.toHilbert) = ‖r‖ * blockNorm z.toHilbert
    exact augmentedNorm_smul (blockSeminorm n) r z.toHilbert
  norm_triangle x y := by
    change blockNorm (x.toHilbert + y.toHilbert) ≤
      blockNorm x.toHilbert + blockNorm y.toHilbert
    exact augmentedNorm_add_le (blockSeminorm n) x.toHilbert y.toHilbert
  norm_eq_zero_iff z := by
    change blockNorm z.toHilbert = 0 ↔ z = 0
    constructor
    · intro hz
      apply ext
      exact (augmentedNorm_eq_zero (blockSeminorm n) z.toHilbert).mp hz
    · rintro rfl
      exact (augmentedNorm_eq_zero (blockSeminorm n) 0).mpr rfl

noncomputable instance (n : ℕ) : NormedAddCommGroup (BlockSpace n) :=
  NormedAddCommGroup.ofCore (normedSpaceCore n)

noncomputable instance (n : ℕ) : NormedSpace ℝ (BlockSpace n) :=
  NormedSpace.ofCore (normedSpaceCore n)

/-- The algebraic identity between the renormed block and its Hilbert model. -/
def linearEquivHilbert (n : ℕ) : BlockSpace n ≃ₗ[ℝ] BlockHilbert n where
  toEquiv := equivHilbert n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem linearEquivHilbert_apply {n : ℕ} (z : BlockSpace n) :
    linearEquivHilbert n z = z.toHilbert :=
  rfl

@[simp]
theorem linearEquivHilbert_symm_apply {n : ℕ} (z : BlockHilbert n) :
    (linearEquivHilbert n).symm z = ⟨z⟩ :=
  rfl

/-- One side of the uniform norm comparison. -/
theorem hilbert_norm_le_norm {n : ℕ} (z : BlockSpace n) :
    ‖z.toHilbert‖ ≤ ‖z‖ :=
  norm_le_blockNorm z.toHilbert

/-- The other side of the uniform norm comparison. -/
theorem norm_le_sqrtThree_mul_hilbert_norm {n : ℕ} (z : BlockSpace n) :
    ‖z‖ ≤ Real.sqrt 3 * ‖z.toHilbert‖ :=
  blockNorm_le_sqrtThree_mul_norm z.toHilbert

/-- The identity between the two models of every block is a continuous linear
equivalence, with constants independent of `n`. -/
noncomputable def continuousLinearEquivHilbert (n : ℕ) :
    BlockSpace n ≃L[ℝ] BlockHilbert n :=
  (linearEquivHilbert n).toContinuousLinearEquivOfBounds 1 (Real.sqrt 3)
    (fun z ↦ by simpa using hilbert_norm_le_norm z)
    (fun z ↦ by simpa using blockNorm_le_sqrtThree_mul_norm z)

/-- Every renormed block is complete by equivalence with its Euclidean model. -/
noncomputable instance (n : ℕ) : CompleteSpace (BlockSpace n) :=
  (completeSpace_congr
    (continuousLinearEquivHilbert n).isUniformEmbedding).mpr inferInstance

/-- Every block is finite-dimensional, independently of its equivalent norm. -/
noncomputable instance (n : ℕ) : FiniteDimensional ℝ (BlockSpace n) :=
  (linearEquivHilbert n).symm.finiteDimensional

end BlockSpace

/-- The paper's space `X = (⊕_n (H_n,N_n))_{ℓ₂}`. -/
abbrev XSpace := lp (fun n : ℕ ↦ BlockSpace n) 2

/-- The `n`th row vector, regarded as an element of the renormed block. -/
noncomputable def rowInBlock {n : ℕ} (i : Fin n) : BlockSpace n :=
  ⟨rowVector i⟩

/-- The `n`th subset vector, regarded as an element of the renormed block. -/
noncomputable def subsetInBlock {n : ℕ} (S : Finset (Fin n)) :
    BlockSpace n :=
  ⟨subsetVector S⟩

@[simp]
theorem rowInBlock_toHilbert {n : ℕ} (i : Fin n) :
    (rowInBlock i).toHilbert = rowVector i :=
  rfl

@[simp]
theorem subsetInBlock_toHilbert {n : ℕ} (S : Finset (Fin n)) :
    (subsetInBlock S).toHilbert = subsetVector S :=
  rfl

@[simp]
theorem norm_rowInBlock {n : ℕ} (i : Fin n) :
    ‖rowInBlock i‖ = Real.sqrt 2 :=
  blockNorm_rowVector i

theorem norm_subsetInBlock_le_sqrtTwo {n : ℕ}
    (S : Finset (Fin n)) :
    ‖subsetInBlock S‖ ≤ Real.sqrt 2 :=
  blockNorm_subsetVector_le_sqrtTwo S

/-- Embed a row into the `n`th summand of `X`. -/
noncomputable def rowInX {n : ℕ} (i : Fin n) : XSpace :=
  lp.single 2 n (rowInBlock i)

/-- Embed a subset parameter into the `n`th summand of `X`. -/
noncomputable def subsetInX {n : ℕ} (S : Finset (Fin n)) : XSpace :=
  lp.single 2 n (subsetInBlock S)

@[simp]
theorem norm_rowInX {n : ℕ} (i : Fin n) :
    ‖rowInX i‖ = Real.sqrt 2 := by
  simp [rowInX, lp.norm_single]

theorem norm_subsetInX_le_sqrtTwo {n : ℕ}
    (S : Finset (Fin n)) :
    ‖subsetInX S‖ ≤ Real.sqrt 2 := by
  simpa [subsetInX, lp.norm_single] using norm_subsetInBlock_le_sqrtTwo S

/-- The exact cube pattern survives the canonical one-block embedding into
`X`. -/
theorem norm_rowInX_add_subsetInX {n : ℕ} (i : Fin n)
    (S : Finset (Fin n)) :
    ‖rowInX i + subsetInX S‖ =
      if i ∈ S then Real.sqrt 6 else Real.sqrt 3 := by
  rw [rowInX, subsetInX, ← lp.single_add,
    lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  change blockNorm (rowVector i + subsetVector S) =
    if i ∈ S then Real.sqrt 6 else Real.sqrt 3
  exact blockNorm_row_add_subset i S

end

end NormFormula.X
