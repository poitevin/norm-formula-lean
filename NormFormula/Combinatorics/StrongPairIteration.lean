import NormFormula.Combinatorics.StrongPairGuarantee

/-!
# Iterating the finite strong-pair recurrence

The fiber recurrence deletes one active row, doubles the guaranteed number of
realized strong pairs, and multiplies the required family size by its finite
pairing constant. This file records the resulting recursive size threshold and
iterates the uniform guarantee for any number of available active rows.
-/

namespace NormFormula

/-- Family-size threshold obtained by iterating the strong-pair recurrence.
The row count decreases at each recursive step because a coordinate fiber is
viewed on the active rows with its defining coordinate erased. -/
def strongPairIterationFamilySize
    (rowCount levelCount : ℕ) : ℕ → ℕ
  | 0 => 2
  | steps + 1 =>
      2 * ((rowCount * levelCount * levelCount) *
        strongPairIterationFamilySize (rowCount - 1) levelCount steps)

@[simp] theorem strongPairIterationFamilySize_zero
    (rowCount levelCount : ℕ) :
    strongPairIterationFamilySize rowCount levelCount 0 = 2 := by
  rfl

@[simp] theorem strongPairIterationFamilySize_succ
    (rowCount levelCount steps : ℕ) :
    strongPairIterationFamilySize rowCount levelCount (steps + 1) =
      2 * ((rowCount * levelCount * levelCount) *
        strongPairIterationFamilySize (rowCount - 1) levelCount steps) := by
  rfl

/-- The iterated family-size threshold is positive whenever the requested
number of recurrence steps does not exceed the available row count. -/
theorem strongPairIterationFamilySize_pos
    {rowCount levelCount steps : ℕ}
    (hlevelCount : 0 < levelCount) (hsteps : steps ≤ rowCount) :
    0 < strongPairIterationFamilySize rowCount levelCount steps := by
  induction steps generalizing rowCount with
  | zero => simp
  | succ steps ih =>
      have hrowCount : 0 < rowCount := by omega
      have hsteps' : steps ≤ rowCount - 1 := by omega
      have hchild := ih hsteps'
      simp only [strongPairIterationFamilySize_succ]
      positivity

/-- After `steps` recurrence levels, every sufficiently large separated class
realizes at least `2^steps` nonempty strong-threshold pairs. -/
theorem guaranteesRealizedStrongPairCount_iteration
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    (activeRows : Finset Row) (levelCount steps : ℕ)
    (hlevelCount : 0 < levelCount) (hsteps : steps ≤ activeRows.card) :
    GuaranteesRealizedStrongPairCount activeRows levelCount
      (strongPairIterationFamilySize activeRows.card levelCount steps)
      (2 ^ steps) := by
  induction steps generalizing activeRows with
  | zero =>
      simpa using
        guaranteesRealizedStrongPairCount_two_one activeRows levelCount
  | succ steps ih =>
      have hactive : activeRows.Nonempty := by
        exact Finset.card_pos.mp (by omega)
      let childFamilySize :=
        strongPairIterationFamilySize (activeRows.card - 1)
          levelCount steps
      have hchildSize : 0 < childFamilySize := by
        apply strongPairIterationFamilySize_pos hlevelCount
        omega
      have hchild : ∀ row ∈ activeRows,
          GuaranteesRealizedStrongPairCount (activeRows.erase row)
            levelCount childFamilySize (2 ^ steps) := by
        intro row hrow
        have hcardErase : (activeRows.erase row).card =
            activeRows.card - 1 := Finset.card_erase_of_mem hrow
        have hstepsErase : steps ≤ (activeRows.erase row).card := by
          omega
        have hih := ih (activeRows.erase row) hstepsErase
        simpa [childFamilySize, hcardErase] using hih
      have hrecurrence := guaranteesRealizedStrongPairCount_step
        hactive hlevelCount hchildSize hchild
      simpa [strongPairIterationFamilySize, childFamilySize, pow_succ,
        Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hrecurrence

end NormFormula
