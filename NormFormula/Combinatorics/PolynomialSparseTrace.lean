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

/-- The bound on one symbolic row list is monotone in the support and label
bounds. -/
theorem symbolicRowFormBound_mono_left (m : ℕ) {ℓ k : ℕ} (hℓ : ℓ ≤ k) :
    symbolicRowFormBound m ℓ ≤ symbolicRowFormBound m k := by
  have hbase : m + ℓ ≤ m + k := Nat.add_le_add_left hℓ m
  have hmul := Nat.mul_le_mul hbase hbase
  unfold symbolicRowFormBound
  omega

/-- The order-type constant is monotone in the number of labels. -/
theorem orderTypeConstant_mono {ℓ k : ℕ} (hℓ : ℓ ≤ k) :
    orderTypeConstant ℓ ≤ orderTypeConstant k := by
  unfold orderTypeConstant
  exact Nat.mul_le_mul
    (pow_le_pow_right' (by omega) hℓ)
    (pow_le_pow_right' (by omega) (Nat.mul_le_mul hℓ hℓ))

/-- A constant depending only on the row-support and parameter-support bounds
for the final degree-`2k` polynomial. -/
def sparseTracePolynomialConstant (m k : ℕ) : ℕ :=
  (k + 1) *
    (orderTypeConstant k *
      (2 * (m + (m + k + 1)) + 1) ^ k *
      ((k + 1) * (4 * symbolicRowFormBound m k) ^ k))

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

/-- The hyperplane-count base for one fixed type is also bounded by a
constant times `n+1`. -/
theorem fixedTraceBase_le (n m : ℕ) {ℓ k : ℕ} (hℓ : ℓ ≤ k) :
    2 * (n * (2 * symbolicRowFormBound m ℓ)) ≤
      (4 * symbolicRowFormBound m k) * (n + 1) := by
  have hL := symbolicRowFormBound_mono_left m hℓ
  have hprod : n * symbolicRowFormBound m ℓ ≤
      (n + 1) * symbolicRowFormBound m k :=
    Nat.mul_le_mul (Nat.le_succ n) hL
  calc
    _ = 4 * (n * symbolicRowFormBound m ℓ) := by ring
    _ ≤ 4 * ((n + 1) * symbolicRowFormBound m k) :=
      Nat.mul_le_mul_left 4 hprod
    _ = _ := by ring

/-- Each summand in the union over label counts is controlled by the common
degree-`2k` monomial. -/
theorem sparseTraceSummand_le_polynomial
    (n m k : ℕ) {ℓ : ℕ} (hℓ : ℓ ≤ k) (D : Finset ℕ)
    (hD : D.card ≤ n * m + (m + k + 1)) :
    Fintype.card (SparseOrderType D ℓ) *
        ((ℓ + 1) *
          (2 * (n * (2 * symbolicRowFormBound m ℓ))) ^ ℓ) ≤
      (orderTypeConstant k *
        (2 * (m + (m + k + 1)) + 1) ^ k *
        ((k + 1) * (4 * symbolicRowFormBound m k) ^ k)) *
          (n + 1) ^ (2 * k) := by
  let A := 2 * (m + (m + k + 1)) + 1
  let B := 4 * symbolicRowFormBound m k
  have hApos : 1 ≤ A * (n + 1) := by
    apply Nat.one_le_iff_ne_zero.mpr
    apply Nat.mul_ne_zero
    · dsimp [A]
      omega
    · omega
  have hBpos : 1 ≤ B * (n + 1) := by
    apply Nat.one_le_iff_ne_zero.mpr
    apply Nat.mul_ne_zero
    · dsimp [B, symbolicRowFormBound]
      omega
    · omega
  have horderPow : (2 * (n * m + (m + k + 1)) + 1) ^ ℓ ≤
      (A * (n + 1)) ^ k := by
    exact (pow_le_pow_left' (by simpa [A] using protectedOrderBase_le n m k) ℓ).trans
      (pow_le_pow_right' hApos hℓ)
  have htracePow : (2 * (n * (2 * symbolicRowFormBound m ℓ))) ^ ℓ ≤
      (B * (n + 1)) ^ k := by
    exact (pow_le_pow_left' (by simpa [B] using fixedTraceBase_le n m hℓ) ℓ).trans
      (pow_le_pow_right' hBpos hℓ)
  have hcode := card_sparseOrderType_le D ℓ
    (n * m + (m + k + 1)) hD
  have hcode' : Fintype.card (SparseOrderType D ℓ) ≤
      orderTypeConstant k * (A * (n + 1)) ^ k :=
    hcode.trans (Nat.mul_le_mul (orderTypeConstant_mono hℓ) horderPow)
  have htrace : (ℓ + 1) *
      (2 * (n * (2 * symbolicRowFormBound m ℓ))) ^ ℓ ≤
      (k + 1) * (B * (n + 1)) ^ k :=
    Nat.mul_le_mul (Nat.add_le_add_right hℓ 1) htracePow
  calc
    _ ≤ (orderTypeConstant k * (A * (n + 1)) ^ k) *
        ((k + 1) * (B * (n + 1)) ^ k) := Nat.mul_le_mul hcode' htrace
    _ = (orderTypeConstant k * A ^ k * ((k + 1) * B ^ k)) *
        (n + 1) ^ (2 * k) := by
      simp only [mul_pow]
      rw [show 2 * k = k + k by omega, pow_add]
      ring
    _ = _ := by rfl

/-- The finite trace collection used for parameters having at most `k`
labelled nonzero coordinates. -/
noncomputable def sparseParameterThresholdTraces
    {ρ : Type*} [Fintype ρ] (m k : ℕ)
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (threshold : ρ → ℝ) : Finset (Finset ρ) :=
  realizableBoundedLabelSparseTypeTraces k
    rowU rowV firstSupport secondSupport threshold
    (sparseTraceProtectedSet firstSupport secondSupport m k)

/-- Every labelled parameter realization with at most `k` coordinates is
covered by the global sparse trace collection. -/
theorem fixedTypeSymbolicThresholdTrace_mem_sparseParameterThresholdTraces
    {ρ : Type*} [Fintype ρ] {ℓ m k : ℕ}
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (threshold : ρ → ℝ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (t : Fin ℓ → ℝ) (hℓ : ℓ ≤ k)
    (hsupport : ∀ r, (firstSupport r).card + (secondSupport r).card ≤ m)
    (hrowU : ∀ r n, n ∉ firstSupport r → rowU r n = 0)
    (hrowV : ∀ r n, n ∉ secondSupport r → rowV r n = 0) :
    fixedTypeSymbolicThresholdTrace
        rowU rowV firstSupport secondSupport copy index threshold t ∈
      sparseParameterThresholdTraces m k
        rowU rowV firstSupport secondSupport threshold := by
  apply fixedTypeSymbolicThresholdTrace_mem_boundedLabelUnion (s := m + k)
    rowU rowV firstSupport secondSupport threshold
    (sparseTraceProtectedSet firstSupport secondSupport m k)
    copy index t hℓ
  · exact firstSupport_subset_sparseTraceProtectedSet
      firstSupport secondSupport m k
  · exact secondSupport_subset_sparseTraceProtectedSet
      firstSupport secondSupport m k
  · exact hrowU
  · exact hrowV
  · intro r
    have hs := hsupport r
    omega
  · exact initialBlock_subset_sparseTraceProtectedSet
      firstSupport secondSupport m k

/-- Supplementary degree-`2k` sparse trace estimate, with an explicit
constant depending only on `m` and `k`. -/
theorem card_sparseParameterThresholdTraces_le_polynomial
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] (m k : ℕ)
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (threshold : ρ → ℝ)
    (hsupport : ∀ r, (firstSupport r).card + (secondSupport r).card ≤ m) :
    (sparseParameterThresholdTraces m k
      rowU rowV firstSupport secondSupport threshold).card ≤
      sparseTracePolynomialConstant m k *
        (Fintype.card ρ + 1) ^ (2 * k) := by
  let D := sparseTraceProtectedSet firstSupport secondSupport m k
  have hD : D.card ≤ Fintype.card ρ * m + (m + k + 1) :=
    card_sparseTraceProtectedSet_le firstSupport secondSupport m k hsupport
  have hsum := card_realizableBoundedLabelSparseTypeTraces_le_sum
    (k := k) (m := m) rowU rowV firstSupport secondSupport threshold D hsupport
  unfold sparseParameterThresholdTraces
  calc
    _ ≤ ∑ ℓ ∈ Finset.range (k + 1),
        Fintype.card (SparseOrderType D ℓ) *
          ((ℓ + 1) *
            (2 * (Fintype.card ρ * (2 * symbolicRowFormBound m ℓ))) ^ ℓ) := hsum
    _ ≤ ∑ _ℓ ∈ Finset.range (k + 1),
        (orderTypeConstant k *
          (2 * (m + (m + k + 1)) + 1) ^ k *
          ((k + 1) * (4 * symbolicRowFormBound m k) ^ k)) *
            (Fintype.card ρ + 1) ^ (2 * k) := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      exact sparseTraceSummand_le_polynomial (Fintype.card ρ) m k
        (by have := Finset.mem_range.mp hℓ; omega) D hD
    _ = sparseTracePolynomialConstant m k *
        (Fintype.card ρ + 1) ^ (2 * k) := by
      simp [sparseTracePolynomialConstant]
      ring

end NormFormula.HalfGraph
