import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NormFormula.Analytic.C0

/-!
# Hilbert spaces contain no isomorphic copy of `c₀`

This file proves directly the final Banach-space exclusion needed in the
paper. If `c₀` embedded into a real inner-product space, the images of its
first `n` unit vectors would all have norm bounded below. A choice of signs
makes the squared norm of their signed sum at least the sum of their squared
norms, while the corresponding signed sum in `c₀` has norm at most one.
Choosing `n` large gives a contradiction.

This finite argument avoids any dependence on the not-yet-formalized
Milman--Pettis theorem.
-/

namespace NormFormula

open scoped ENNReal InnerProductSpace

noncomputable section

/-- The `i`-th standard unit vector of the concrete `C0Space`. -/
def c0Basis (i : ℕ) : C0Space :=
  ⟨lp.single ∞ i (1 : ℝ), by
    apply tendsto_atTop_of_eventually_const (i₀ := i + 1)
    intro j hj
    exact lp.single_apply_ne ∞ i 1 (by omega)⟩


@[simp]
theorem norm_c0Basis (i : ℕ) : ‖c0Basis i‖ = 1 := by
  change ‖lp.single (E := fun _ : ℕ ↦ ℝ) ∞ i (1 : ℝ)‖ = 1
  rw [lp.norm_single (p := ∞) (by simp)]
  norm_num

/-- A finite signed sum of distinct standard `c₀` unit vectors has norm at
most one. -/
theorem norm_sum_smul_c0Basis_le_one
    {n : ℕ} (sign : Fin n → ℝ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1) :
    ‖∑ i, sign i • c0Basis i.1‖ ≤ 1 := by
  classical
  change ‖((↑(∑ i, sign i • c0Basis i.1) : C0Space) :
    BoundedScalarSequences)‖ ≤ 1
  apply lp.norm_le_of_forall_le zero_le_one
  intro j
  by_cases hj : j < n
  · let i : Fin n := ⟨j, hj⟩
    have hvalue :
        ((↑(∑ k, sign k • c0Basis k.1) : C0Space) :
          BoundedScalarSequences) j = sign i := by
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower,
        lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply]
      change (∑ k : Fin n,
        sign k * (lp.single (E := fun _ : ℕ ↦ ℝ) ∞ k.1 (1 : ℝ)) j) = sign i
      rw [Finset.sum_eq_single i]
      · simp [i]
      · intro b _ hbi
        rw [lp.single_apply_ne]
        · simp
        · exact fun hbj ↦ hbi (Fin.ext hbj.symm)
      · simp
    rw [hvalue]
    rcases hsign i with hi | hi <;> simp [hi]
  · have hvalue :
        ((↑(∑ k, sign k • c0Basis k.1) : C0Space) :
          BoundedScalarSequences) j = 0 := by
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower,
        lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply]
      change (∑ k : Fin n,
        sign k * (lp.single (E := fun _ : ℕ ↦ ℝ) ∞ k.1 (1 : ℝ)) j) = 0
      apply Finset.sum_eq_zero
      intro i _
      rw [lp.single_apply_ne]
      · simp
      · exact fun hji ↦ hj (hji.symm ▸ i.2)
    rw [hvalue]
    norm_num

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Signs can be chosen so that a finite signed sum in a real inner-product
space has squared norm at least the sum of the individual squared norms. -/
theorem exists_sign_sum_norm_sq_ge {n : ℕ} (v : Fin n → H) :
    ∃ sign : Fin n → ℝ,
      (∀ i, sign i = 1 ∨ sign i = -1) ∧
      ∑ i, ‖v i‖ ^ 2 ≤ ‖∑ i, sign i • v i‖ ^ 2 := by
  classical
  let s : Finset (Fin n) := Finset.univ
  suffices ∃ sign : Fin n → ℝ,
      (∀ i ∈ s, sign i = 1 ∨ sign i = -1) ∧
      ∑ i ∈ s, ‖v i‖ ^ 2 ≤ ‖∑ i ∈ s, sign i • v i‖ ^ 2 by
    simpa [s] using this
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨fun _ ↦ 1, ?_, by simp⟩
      simp
  | @insert a s ha ih =>
      obtain ⟨sign, hsign, hbound⟩ := ih
      let w : H := ∑ i ∈ s, sign i • v i
      let aSign : ℝ := if 0 ≤ ⟪v a, w⟫_ℝ then 1 else -1
      let sign' : Fin n → ℝ := Function.update sign a aSign
      have haSign : aSign = 1 ∨ aSign = -1 := by
        dsimp [aSign]
        split_ifs <;> simp
      have hcross : 0 ≤ ⟪aSign • v a, w⟫_ℝ := by
        rw [real_inner_smul_left]
        dsimp [aSign]
        split_ifs with h <;> simp <;> linarith
      have hsum : ∑ i ∈ insert a s, sign' i • v i = aSign • v a + w := by
        rw [Finset.sum_insert ha]
        rw [show sign' a = aSign by simp [sign']]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [show sign' i = sign i by
          apply Function.update_of_ne
          exact fun hia ↦ ha (hia ▸ hi)]
      refine ⟨sign', ?_, ?_⟩
      · intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · simpa [sign'] using haSign
        · have hia : i ≠ a := fun hia ↦ ha (hia ▸ hi)
          simpa [sign', Function.update_of_ne hia] using hsign i hi
      · rw [hsum, Finset.sum_insert ha, norm_add_sq_real]
        have haSignNorm : ‖aSign • v a‖ ^ 2 = ‖v a‖ ^ 2 := by
          rcases haSign with h | h <;> rw [h] <;> simp
        rw [haSignNorm]
        dsimp [w] at hbound ⊢
        linarith

/-- No real inner-product space contains an isomorphic copy of `c₀`. -/
theorem innerProductSpace_not_containsIsomorphicCopyOfC0 :
    ¬ ContainsIsomorphicCopyOfC0 H := by
  rintro ⟨T, c, hc, hT⟩
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (‖T‖ ^ 2 / c ^ 2)
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hlarge : ‖T‖ ^ 2 < (n : ℝ) * c ^ 2 := by
    exact (div_lt_iff₀ hc2).mp hn
  let v : Fin n → H := fun i ↦ T (c0Basis i.1)
  obtain ⟨sign, hsign, hsumLower⟩ := exists_sign_sum_norm_sq_ge v
  let z : C0Space := ∑ i, sign i • c0Basis i.1
  have hz : ‖z‖ ≤ 1 := norm_sum_smul_c0Basis_le_one sign hsign
  have himage : T z = ∑ i, sign i • v i := by
    simp [z, v, map_sum]
  have hsumUpper : ‖∑ i, sign i • v i‖ ≤ ‖T‖ := by
    rw [← himage]
    exact @ContinuousLinearMap.unit_le_opNorm
      ℝ ℝ C0Space H _ _ _ _ instNormedSpaceC0Space _
      (RingHom.id ℝ) _ T z hz
  have hTnonneg : 0 ≤ ‖T‖ := (norm_nonneg (∑ i, sign i • v i)).trans hsumUpper
  have hsumUpperSq : ‖∑ i, sign i • v i‖ ^ 2 ≤ ‖T‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hTnonneg).2 hsumUpper
  have hvLower : ∀ i, c ^ 2 ≤ ‖v i‖ ^ 2 := by
    intro i
    have hbasis :
        ‖(↑(c0Basis i.1) : BoundedScalarSequences)‖ = 1 :=
      norm_c0Basis i.1
    have hci : c ≤ ‖v i‖ := by
      calc
        c = c * 1 := by ring
        _ = c * ‖(↑(c0Basis i.1) : BoundedScalarSequences)‖ := by rw [hbasis]
        _ ≤ ‖v i‖ := by simpa [v] using hT (c0Basis i.1)
    exact (sq_le_sq₀ hc.le (norm_nonneg _)).2 hci
  have hcardLower : (n : ℝ) * c ^ 2 ≤ ∑ i, ‖v i‖ ^ 2 := by
    calc
      (n : ℝ) * c ^ 2 = ∑ _i : Fin n, c ^ 2 := by simp
      _ ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_le_sum fun i _ ↦ hvLower i
  exact (not_lt_of_ge (hcardLower.trans (hsumLower.trans hsumUpperSq))) hlarge

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The exclusion of `c₀` transfers across a continuous linear equivalence
whose inverse has a positive norm bound. -/
theorem not_containsIsomorphicCopyOfC0_of_equiv_innerProduct
    (e : W ≃L[ℝ] H) (K : ℝ) (hK : 0 < K)
    (hinv : ∀ h : H, ‖e.symm h‖ ≤ K * ‖h‖) :
    ¬ ContainsIsomorphicCopyOfC0 W := by
  rintro ⟨T, c, hc, hT⟩
  apply innerProductSpace_not_containsIsomorphicCopyOfC0 (H := H)
  refine ⟨e.toContinuousLinearMap.comp T, c / K, div_pos hc hK, ?_⟩
  intro x
  change (c / K) * ‖x‖ ≤ ‖e (T x)‖
  have hinv' : ‖T x‖ ≤ K * ‖e (T x)‖ := by
    simpa using hinv (e (T x))
  rw [div_mul_eq_mul_div, div_le_iff₀ hK]
  simpa [mul_comm] using (hT x).trans hinv'

end

end NormFormula
