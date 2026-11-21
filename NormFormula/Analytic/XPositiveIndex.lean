import NormFormula.Analytic.XSpace

/-!
# The positive-index sum of the renormed blocks

The empty-subset coordinate contributes only its Euclidean square to each
block norm squared. Move this coordinate from block `n` to block `n + 1`
and keep every other coordinate in its original block. This identifies the
sum over all natural numbers isometrically with the paper's sum over the
positive natural numbers.
-/

namespace NormFormula.X

noncomputable section

/-- The paper's `X`, with block dimensions `1, 2, …`. -/
abbrev XPositiveSpace := lp (fun n : ℕ ↦ BlockSpace (n + 1)) 2

private def emptyIndex (n : ℕ) : BlockIndex n := Sum.inr ∅

private def emptyCoordinate {n : ℕ} (z : BlockSpace n) : ℝ :=
  z.toHilbert (emptyIndex n)

private def replaceEmpty {n : ℕ} (z : BlockSpace n) (a : ℝ) : BlockSpace n :=
  ⟨WithLp.toLp 2 (fun i ↦ if i = emptyIndex n then a else z.toHilbert i)⟩

@[simp] private theorem replaceEmpty_apply {n : ℕ} (z : BlockSpace n)
    (a : ℝ) (i : BlockIndex n) :
    (replaceEmpty z a).toHilbert i = if i = emptyIndex n then a else z.toHilbert i :=
  rfl

@[simp] private theorem emptyCoordinate_replaceEmpty {n : ℕ} (z : BlockSpace n) (a : ℝ) :
    emptyCoordinate (replaceEmpty z a) = a := by
  simp [emptyCoordinate]

@[simp] private theorem replaceEmpty_replaceEmpty {n : ℕ} (z : BlockSpace n) (a b : ℝ) :
    replaceEmpty (replaceEmpty z a) b = replaceEmpty z b := by
  ext i
  by_cases hi : i = emptyIndex n <;> simp [hi]

@[simp] private theorem replaceEmpty_self {n : ℕ} (z : BlockSpace n) :
    replaceEmpty z (emptyCoordinate z) = z := by
  ext i
  by_cases hi : i = emptyIndex n <;> simp [hi, emptyCoordinate]

private theorem eq_emptyIndex_zero (i : BlockIndex 0) : i = emptyIndex 0 := by
  rcases i with i | S
  · exact Fin.elim0 i
  · have hS : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i ↦ Fin.elim0 i)
    simp [emptyIndex, hS]

private theorem blockSeminorm_replaceEmpty {n : ℕ} (z : BlockSpace n) (a : ℝ) :
    blockSeminorm n (replaceEmpty z a).toHilbert = blockSeminorm n z.toHilbert := by
  have hpair (p : BlockPair n) :
      pairSeminorm p.1.1 p.1.2 (replaceEmpty z a).toHilbert =
        pairSeminorm p.1.1 p.1.2 z.toHilbert := by
    have hS : p.1.2 ≠ ∅ := Finset.ne_empty_of_mem p.2
    simp [emptyIndex, hS]
  apply le_antisymm <;> apply Seminorm.finset_sup_apply_le (by positivity)
  · intro p _
    rw [hpair p]
    exact pairSeminorm_le_blockSeminorm p z.toHilbert
  · intro p _
    rw [← hpair p]
    exact pairSeminorm_le_blockSeminorm p (replaceEmpty z a).toHilbert

private def remainingSquare {n : ℕ} (z : BlockSpace n) : ℝ :=
  (∑ i ∈ (Finset.univ : Finset (BlockIndex n)).erase (emptyIndex n), z.toHilbert i ^ 2) +
    blockSeminorm n z.toHilbert ^ 2

private theorem remainingSquare_nonneg {n : ℕ} (z : BlockSpace n) :
    0 ≤ remainingSquare z := by
  unfold remainingSquare
  positivity

private theorem remainingSquare_zeroBlock (z : BlockSpace 0) : remainingSquare z = 0 := by
  have h : (Finset.univ : Finset (BlockIndex 0)).erase (emptyIndex 0) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i
    simp [eq_emptyIndex_zero i]
  haveI : IsEmpty (BlockPair 0) := ⟨fun p ↦ Fin.elim0 p.1.1⟩
  simp [remainingSquare, h, blockSeminorm]

private theorem norm_replaceEmpty_sq {n : ℕ} (z : BlockSpace n) (a : ℝ) :
    ‖replaceEmpty z a‖ ^ 2 = remainingSquare z + a ^ 2 := by
  rw [BlockSpace.norm_def, blockNorm, augmentedNorm, Real.sq_sqrt (by positivity),
    EuclideanSpace.real_norm_sq_eq, blockSeminorm_replaceEmpty]
  rw [← Finset.sum_erase_add Finset.univ (fun i ↦ (replaceEmpty z a).toHilbert i ^ 2)
    (Finset.mem_univ (emptyIndex n))]
  have hsum :
      ∑ i ∈ (Finset.univ : Finset (BlockIndex n)).erase (emptyIndex n),
          (replaceEmpty z a).toHilbert i ^ 2 =
        ∑ i ∈ (Finset.univ : Finset (BlockIndex n)).erase (emptyIndex n),
          z.toHilbert i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [(Finset.mem_erase.mp hi).1]
  rw [hsum, replaceEmpty_apply, if_pos rfl, remainingSquare]
  ring

private theorem norm_block_sq {n : ℕ} (z : BlockSpace n) :
    ‖z‖ ^ 2 = remainingSquare z + emptyCoordinate z ^ 2 := by
  simpa only [replaceEmpty_self] using norm_replaceEmpty_sq z (emptyCoordinate z)

private theorem summable_blockSquares {B : ℕ → Type*} [∀ n, NormedAddCommGroup (B n)]
    (x : lp B 2) : Summable (fun n ↦ ‖x n‖ ^ 2) := by
  simpa using (lp.memℓp x).summable (by norm_num : 0 < (2 : ENNReal).toReal)

private theorem summable_remainingSquares {d : ℕ → ℕ}
    (x : lp (fun n ↦ BlockSpace (d n)) 2) :
    Summable (fun n ↦ remainingSquare (x n)) :=
  Summable.of_nonneg_of_le (fun n ↦ remainingSquare_nonneg (x n))
    (fun n ↦ by rw [norm_block_sq]; exact le_add_of_nonneg_right (sq_nonneg _))
    (summable_blockSquares x)

private theorem summable_emptySquares {d : ℕ → ℕ}
    (x : lp (fun n ↦ BlockSpace (d n)) 2) :
    Summable (fun n ↦ emptyCoordinate (x n) ^ 2) :=
  Summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _)
    (fun n ↦ by rw [norm_block_sq]; exact le_add_of_nonneg_left (remainingSquare_nonneg _))
    (summable_blockSquares x)

private def shiftEmptyForward (x : XSpace) : XPositiveSpace := by
  refine ⟨fun n ↦ replaceEmpty (x (n + 1)) (emptyCoordinate (x n)), ?_⟩
  apply memℓp_gen
  have hs := (summable_nat_add_iff 1).mpr
    (summable_remainingSquares (d := id) x)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_replaceEmpty_sq] using
    hs.add (summable_emptySquares (d := id) x)

private def shiftEmptyBackward (x : XPositiveSpace) : XSpace := by
  let blocks : ∀ n : ℕ, BlockSpace n
    | 0 => replaceEmpty 0 (emptyCoordinate (x 0))
    | n + 1 => replaceEmpty (x n) (emptyCoordinate (x (n + 1)))
  refine ⟨blocks, ?_⟩
  apply memℓp_gen
  apply (summable_nat_add_iff 1).mp
  change Summable (fun n ↦ ‖replaceEmpty (x n) (emptyCoordinate (x (n + 1)))‖ ^
    (2 : ENNReal).toReal)
  have hs := (summable_nat_add_iff 1).mpr
    (summable_emptySquares (d := fun n ↦ n + 1) x)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_replaceEmpty_sq] using
    (summable_remainingSquares (d := fun n ↦ n + 1) x).add hs

private theorem norm_shiftEmptyForward (x : XSpace) : ‖shiftEmptyForward x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hnorm {B : ℕ → Type} [∀ n, NormedAddCommGroup (B n)] (z : lp B 2) :
      ‖z‖ ^ 2 = ∑' n, ‖z n‖ ^ 2 := by
    simpa [Real.rpow_two] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) z
  rw [hnorm (shiftEmptyForward x), hnorm x]
  have hrem : Summable (fun n ↦ remainingSquare (x n)) :=
    summable_remainingSquares (d := id) x
  have htail : Summable (fun n ↦ remainingSquare (x (n + 1))) :=
    (summable_nat_add_iff 1).mpr hrem
  have hempty : Summable (fun n ↦ emptyCoordinate (x n) ^ 2) :=
    summable_emptySquares (d := id) x
  calc
    (∑' n, ‖shiftEmptyForward x n‖ ^ 2) =
        ∑' n, (remainingSquare (x (n + 1)) + emptyCoordinate (x n) ^ 2) := by
      apply tsum_congr
      intro n
      exact norm_replaceEmpty_sq _ _
    _ = (∑' n, remainingSquare (x (n + 1))) + ∑' n, emptyCoordinate (x n) ^ 2 :=
      htail.tsum_add hempty
    _ = (∑' n, remainingSquare (x n)) + ∑' n, emptyCoordinate (x n) ^ 2 := by
      rw [hrem.tsum_eq_zero_add, remainingSquare_zeroBlock, zero_add]
    _ = ∑' n, ‖x n‖ ^ 2 := by
      rw [← hrem.tsum_add hempty]
      exact tsum_congr (fun n ↦ (norm_block_sq (x n)).symm)

/-- A surjective real linear isometry obtained by moving the empty-subset
coordinate of block `n` to block `n + 1`. -/
def xSpaceEquivPositive : XSpace ≃ₗᵢ[ℝ] XPositiveSpace where
  toFun := shiftEmptyForward
  invFun := shiftEmptyBackward
  left_inv x := by
    apply lp.ext
    funext n
    cases n with
    | zero =>
        apply BlockSpace.ext
        ext i
        rw [eq_emptyIndex_zero i]
        change emptyCoordinate (replaceEmpty (0 : BlockSpace 0)
          (emptyCoordinate (replaceEmpty (x 1) (emptyCoordinate (x 0))))) = _
        simp [emptyCoordinate]
    | succ n =>
        change replaceEmpty (replaceEmpty (x (n + 1)) (emptyCoordinate (x n)))
          (emptyCoordinate (replaceEmpty (x (n + 2)) (emptyCoordinate (x (n + 1))))) = _
        simp
  right_inv x := by
    apply lp.ext
    funext n
    cases n with
    | zero =>
        change replaceEmpty (replaceEmpty (x 0) (emptyCoordinate (x 1)))
          (emptyCoordinate (replaceEmpty (0 : BlockSpace 0) (emptyCoordinate (x 0)))) = _
        simp
    | succ n =>
        change replaceEmpty (replaceEmpty (x (n + 1)) (emptyCoordinate (x (n + 2))))
          (emptyCoordinate (replaceEmpty (x n) (emptyCoordinate (x (n + 1))))) = _
        simp
  map_add' x y := by
    apply lp.ext
    funext n
    apply BlockSpace.ext
    ext i
    change (replaceEmpty (x (n + 1) + y (n + 1)) (emptyCoordinate (x n + y n))).toHilbert i =
      (replaceEmpty (x (n + 1)) (emptyCoordinate (x n)) +
        replaceEmpty (y (n + 1)) (emptyCoordinate (y n))).toHilbert i
    by_cases hi : i = emptyIndex (n + 1) <;> simp [hi, emptyCoordinate, PiLp.add_apply]
  map_smul' c x := by
    apply lp.ext
    funext n
    apply BlockSpace.ext
    ext i
    change (replaceEmpty (c • x (n + 1)) (emptyCoordinate (c • x n))).toHilbert i =
      (c • replaceEmpty (x (n + 1)) (emptyCoordinate (x n))).toHilbert i
    by_cases hi : i = emptyIndex (n + 1) <;> simp [hi, emptyCoordinate, PiLp.smul_apply]
  norm_map' := norm_shiftEmptyForward

end

end NormFormula.X
