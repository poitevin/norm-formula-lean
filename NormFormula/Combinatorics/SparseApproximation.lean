import Mathlib.Data.NNReal.Defs
import NormFormula.Combinatorics.FatShattering
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sparse approximation and finite fat-shattering dimension

The criterion of Section 4.2 is proved for an arbitrary normed additive group
and an arbitrary notion of support size. The final specialization uses the
support in a fixed Hilbert basis. The trace constants and exponents may be
real, as in the paper; enlarging them to natural numbers allows use of the
elementary exponential-versus-polynomial estimate.
-/

namespace NormFormula

theorem exists_real_polynomial_lt_two_pow_bound (A d : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → A * ((n : ℝ) + 1) ^ d < (2 : ℝ) ^ n := by
  obtain ⟨N, hN⟩ := exists_polynomial_lt_two_pow_bound ⌈A⌉₊ ⌈d⌉₊
  refine ⟨N, fun n hn ↦ ?_⟩
  have hp : ((n : ℝ) + 1) ^ d ≤ ((n : ℝ) + 1) ^ ⌈d⌉₊ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (Nat.le_ceil d)
  have hround : A * ((n : ℝ) + 1) ^ d ≤
      (⌈A⌉₊ : ℝ) * ((n : ℝ) + 1) ^ ⌈d⌉₊ :=
    mul_le_mul (Nat.le_ceil A) hp (Real.rpow_nonneg (by positivity) _) (by positivity)
  have hexp : (⌈A⌉₊ : ℝ) * ((n : ℝ) + 1) ^ ⌈d⌉₊ < (2 : ℝ) ^ n := by
    exact_mod_cast hN n hn
  exact hround.trans_lt hexp

/-- Polynomial counting for parameters of bounded support. There is no norm
restriction on the sparse parameters, and thresholds are arbitrary reals. -/
def HasPolynomialSparseTraces {K : Type*} [Add K]
    (p : K → ℝ) (sparse : ℕ → K → Prop) : Prop :=
  ∀ m k : ℕ, ∃ A d : ℝ, 1 ≤ A ∧ 0 ≤ d ∧
    ∀ (n : ℕ) (rows : Fin n → K) (threshold : Fin n → ℝ),
      (∀ r, sparse m (rows r)) → ∃ traces : Finset (Finset (Fin n)),
        (traces.card : ℝ) ≤ A * ((n : ℝ) + 1) ^ d ∧
        ∀ y, sparse k y → thresholdTrace (fun r y ↦ p (rows r + y)) threshold y ∈ traces

/-- Sparse approximation with uniform error tending to zero gives a uniform
finite fat-shattering bound on every pair of closed balls. -/
theorem sparse_approximation_criterion
    {K : Type*} [NormedAddCommGroup K]
    (p : K → ℝ) (sparse : ℕ → K → Prop)
    (P : ℝ → K → K) (a : ℝ → ℝ → ℕ) (ω : ℝ → ℝ)
    (hsupport : ∀ η, 0 < η → ∀ C, 0 ≤ C → ∀ z, ‖z‖ ≤ C → sparse (a C η) (P η z))
    (herror : ∀ η, 0 < η → ∀ x y, |p (x + y) - p (P η x + P η y)| ≤ ω η)
    (hω : Filter.Tendsto ω (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (htraces : HasPolynomialSparseTraces p sparse)
    (R_x R_y ε : ℝ) (hRx : 0 ≤ R_x) (hRy : 0 ≤ R_y) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (n : ℕ) (rows : Fin n → K), (∀ r, ‖rows r‖ ≤ R_x) →
      IsFatShattered (fun r (y : {y : K // ‖y‖ ≤ R_y}) ↦ p (rows r + y.1)) ε → n < N := by
  have hevent : ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < η ∧ ω η < ε := by
    filter_upwards [self_mem_nhdsWithin, hω.eventually (gt_mem_nhds hε)] with η hη hωη
    exact ⟨hη, hωη⟩
  obtain ⟨η, hη, hmargin⟩ := hevent.exists
  obtain ⟨A, d, hA, hd, hcount⟩ := htraces (a R_x η) (a R_y η)
  obtain ⟨N, hN⟩ := exists_real_polynomial_lt_two_pow_bound A d
  refine ⟨N, fun n rows hrows hfat ↦ ?_⟩
  obtain ⟨threshold, hfat⟩ := hfat
  obtain ⟨traces, hcard, hcover⟩ := hcount n (fun r ↦ P η (rows r)) threshold
    (fun r ↦ hsupport η hη R_x hRx (rows r) (hrows r))
  have hlower : 2 ^ n ≤ traces.card := by
    have h := two_pow_card_le_trace_cover_of_fat_witness hfat
      (approxValue := fun r y ↦ p (P η (rows r) + y))
      (approx := fun y : {y : K // ‖y‖ ≤ R_y} ↦ P η y.1)
      (fun r y ↦ (herror η hη (rows r) y.1).trans_lt hmargin)
      (fun y ↦ hcover _ (hsupport η hη R_y hRy y.1 y.2))
    simpa using h
  by_contra hn
  have hsmall := hN n (Nat.le_of_not_gt hn)
  have hlarge : (2 : ℝ) ^ n ≤ (traces.card : ℝ) := by exact_mod_cast hlower
  linarith

/-- Finite support in the fixed orthonormal basis, including the finiteness
condition so that infinite supports are never counted as zero. -/
def HasHilbertSupportSize {ι K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (b : HilbertBasis ι ℝ K) (m : ℕ) (z : K) : Prop :=
  (Function.support (b.repr z)).Finite ∧ (Function.support (b.repr z)).ncard ≤ m

/-- The paper's general sparse-approximation criterion for a Hilbert space
with any fixed orthonormal basis and a nonnegative real-valued function. -/
theorem hilbert_sparse_approximation_criterion
    {ι K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (b : HilbertBasis ι ℝ K) (p : K → NNReal)
    (P : ℝ → K → K) (a : ℝ → ℝ → ℕ) (ω : ℝ → ℝ)
    (hsupport : ∀ η, 0 < η → ∀ C, 0 ≤ C → ∀ z, ‖z‖ ≤ C →
      HasHilbertSupportSize b (a C η) (P η z))
    (herror : ∀ η, 0 < η → ∀ x y,
      |(p (x + y) : ℝ) - (p (P η x + P η y) : ℝ)| ≤ ω η)
    (hω : Filter.Tendsto ω (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (htraces : HasPolynomialSparseTraces (fun z ↦ (p z : ℝ)) (HasHilbertSupportSize b))
    (R_x R_y ε : ℝ) (hRx : 0 ≤ R_x) (hRy : 0 ≤ R_y) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (n : ℕ) (rows : Fin n → K), (∀ r, ‖rows r‖ ≤ R_x) →
      IsFatShattered (fun r (y : {y : K // ‖y‖ ≤ R_y}) ↦ (p (rows r + y.1) : ℝ)) ε → n < N :=
  sparse_approximation_criterion (fun z ↦ (p z : ℝ)) (HasHilbertSupportSize b)
    P a ω hsupport herror hω htraces R_x R_y ε hRx hRy hε

end NormFormula
