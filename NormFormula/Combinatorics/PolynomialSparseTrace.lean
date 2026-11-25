import NormFormula.Combinatorics.SparseTraceUnion

/-!
# The degree-`2k` sparse trace bound

This file chooses the protected set from the row supports and simplifies the
finite sum over label counts and sparse order types to one explicit polynomial
of degree `2k` in the number of rows.
-/

namespace NormFormula.HalfGraph

/-- The numerical indices used by either copy of one row. -/
def combinedRowSupport {ρ : Type*}
    (firstSupport secondSupport : ρ → Finset ℕ) (r : ρ) : Finset ℕ :=
  firstSupport r ∪ secondSupport r

/-- The row-index union together with the protected initial block required by
the `hasZeroBefore` transport argument. -/
def sparseTraceProtectedSet {ρ : Type*} [Fintype ρ]
    (firstSupport secondSupport : ρ → Finset ℕ) (m k : ℕ) : Finset ℕ :=
  protectedIndexSet
    (rowIndexSet (combinedRowSupport firstSupport secondSupport))
    (m + k + 1)

theorem card_combinedRowSupport_le
    {ρ : Type*} [Fintype ρ]
    (firstSupport secondSupport : ρ → Finset ℕ) (m : ℕ)
    (hsupport : ∀ r, (firstSupport r).card + (secondSupport r).card ≤ m)
    (r : ρ) :
    (combinedRowSupport firstSupport secondSupport r).card ≤ m := by
  exact (Finset.card_union_le _ _).trans (hsupport r)

/-- Linear cardinality bound for the protected set. -/
theorem card_sparseTraceProtectedSet_le
    {ρ : Type*} [Fintype ρ]
    (firstSupport secondSupport : ρ → Finset ℕ) (m k : ℕ)
    (hsupport : ∀ r, (firstSupport r).card + (secondSupport r).card ≤ m) :
    (sparseTraceProtectedSet firstSupport secondSupport m k).card ≤
      Fintype.card ρ * m + (m + k + 1) := by
  exact card_protectedRowIndexSet_le
    (combinedRowSupport firstSupport secondSupport) m (m + k + 1)
    (card_combinedRowSupport_le firstSupport secondSupport m hsupport)

theorem firstSupport_subset_sparseTraceProtectedSet
    {ρ : Type*} [Fintype ρ]
    (firstSupport secondSupport : ρ → Finset ℕ) (m k : ℕ) (r : ρ) :
    firstSupport r ⊆ sparseTraceProtectedSet firstSupport secondSupport m k := by
  intro n hn
  apply Finset.mem_union_left
  rw [rowIndexSet, Finset.mem_biUnion]
  exact ⟨r, Finset.mem_univ r, Finset.mem_union_left _ hn⟩

theorem secondSupport_subset_sparseTraceProtectedSet
    {ρ : Type*} [Fintype ρ]
    (firstSupport secondSupport : ρ → Finset ℕ) (m k : ℕ) (r : ρ) :
    secondSupport r ⊆ sparseTraceProtectedSet firstSupport secondSupport m k := by
  intro n hn
  apply Finset.mem_union_left
  rw [rowIndexSet, Finset.mem_biUnion]
  exact ⟨r, Finset.mem_univ r, Finset.mem_union_right _ hn⟩

theorem initialBlock_subset_sparseTraceProtectedSet
    {ρ : Type*} [Fintype ρ]
    (firstSupport secondSupport : ρ → Finset ℕ) (m k : ℕ) :
    Finset.range (m + k + 1) ⊆
      sparseTraceProtectedSet firstSupport secondSupport m k := by
  intro n hn
  exact Finset.mem_union_right _ hn


/-- The order-type constant is monotone in the number of labels. -/
theorem orderTypeConstant_mono {ℓ k : ℕ} (hℓ : ℓ ≤ k) :
    orderTypeConstant ℓ ≤ orderTypeConstant k := by
  unfold orderTypeConstant
  exact Nat.mul_le_mul
    (pow_le_pow_right' (by omega) hℓ)
    (pow_le_pow_right' (by omega) (Nat.mul_le_mul hℓ hℓ))


/-- The affine expression in the protected-set count is bounded by a constant
times `n+1`. -/
theorem protectedOrderBase_le (n m k : ℕ) :
    2 * (n * m + (m + k + 1)) + 1 ≤
      (2 * (m + (m + k + 1)) + 1) * (n + 1) := by
  have hn : n * m ≤ (n + 1) * m :=
    Nat.mul_le_mul_right m (Nat.le_succ n)
  have hr : m + k + 1 ≤ (n + 1) * (m + k + 1) := by
    have h := Nat.mul_le_mul_right (m + k + 1) (show 1 ≤ n + 1 by omega)
    simpa only [one_mul] using h
  have hsum : n * m + (m + k + 1) ≤
      (n + 1) * (m + (m + k + 1)) := by
    calc
      _ ≤ (n + 1) * m + (n + 1) * (m + k + 1) :=
        Nat.add_le_add hn hr
      _ = _ := by ring
  calc
    _ ≤ 2 * ((n + 1) * (m + (m + k + 1))) + (n + 1) :=
      Nat.add_le_add (Nat.mul_le_mul_left 2 hsum) (by omega)
    _ = _ := by ring


end NormFormula.HalfGraph
