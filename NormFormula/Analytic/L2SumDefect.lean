import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Norm-square defects in dependent `ℓ₂`-sums

This file isolates the analytic estimate used in the paper's proof that its
distinguished `ℓ₂`-sum is locally stable.  In every normed space, the failure
of the squared norm to satisfy the Pythagorean identity is bounded by the
product of the two norms.  For a dependent `ℓ₂`-sum we also define the finite
head and complementary tail, prove that the tails converge to zero, and
specialize the defect estimate to them.
-/

namespace NormFormula

noncomputable section

open Filter
open scoped Topology

/-- The defect of the squared norm from the Pythagorean identity. -/
def normSqDefect {E : Type*} [NormedAddCommGroup E] (u v : E) : ℝ :=
  ‖u + v‖ ^ 2 - ‖u‖ ^ 2 - ‖v‖ ^ 2

/-- In an arbitrary normed space, the norm-square defect is bounded by twice
the product of the two norms. -/
theorem abs_normSqDefect_le {E : Type*} [NormedAddCommGroup E] (u v : E) :
    |normSqDefect u v| ≤ 2 * ‖u‖ * ‖v‖ := by
  have htri : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le u v
  have htriSq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg (u + v)) (by positivity)).2 htri
  have hrev : |‖u‖ - ‖v‖| ≤ ‖u + v‖ := by
    simpa [sub_eq_add_neg] using (abs_norm_sub_norm_le u (-v))
  have hrevSq : |‖u‖ - ‖v‖| ^ 2 ≤ ‖u + v‖ ^ 2 :=
    (sq_le_sq₀ (abs_nonneg (‖u‖ - ‖v‖)) (norm_nonneg (u + v))).2 hrev
  rw [abs_le]
  constructor
  · rw [sq_abs] at hrevSq
    dsimp [normSqDefect]
    nlinarith
  · dsimp [normSqDefect]
    nlinarith

section L2Sum

variable {ι : Type*} {E : ι → Type*}
variable [∀ i, NormedAddCommGroup (E i)]
variable [DecidableEq ι]

/-- The finite head of a vector in a dependent `ℓ₂`-sum. -/
def lpHead (s : Finset ι) (f : lp E 2) : lp E 2 :=
  ∑ i ∈ s, lp.single 2 i (f i)

/-- The complementary tail of a vector in a dependent `ℓ₂`-sum. -/
def lpTail (s : Finset ι) (f : lp E 2) : lp E 2 :=
  f - lpHead s f

@[simp]
theorem lpHead_empty (f : lp E 2) : lpHead ∅ f = 0 := by
  simp [lpHead]

@[simp]
theorem lpTail_empty (f : lp E 2) : lpTail ∅ f = f := by
  simp [lpTail]

/-- Finite heads respect addition. -/
theorem lpHead_add (s : Finset ι) (u v : lp E 2) :
    lpHead s (u + v) = lpHead s u + lpHead s v := by
  unfold lpHead
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← lp.single_add]
  congr

/-- Complementary tails respect addition. -/
theorem lpTail_add (s : Finset ι) (u v : lp E 2) :
    lpTail s (u + v) = lpTail s u + lpTail s v := by
  rw [lpTail, lpHead_add]
  simp only [lpTail]
  abel

/-- Finite heads converge to the original vector as the finite set tends to
all indices. -/
theorem tendsto_lpHead (f : lp E 2) :
    Tendsto (fun s : Finset ι ↦ lpHead s f) atTop (𝓝 f) := by
  simpa [lpHead] using
    (lp.hasSum_single (p := (2 : ENNReal)) (by norm_num) f)

/-- Complementary tails converge to zero in the `ℓ₂` norm. -/
theorem tendsto_lpTail_zero (f : lp E 2) :
    Tendsto (fun s : Finset ι ↦ lpTail s f) atTop (𝓝 0) := by
  have h := (tendsto_lpHead f).const_sub f
  simpa [lpTail] using h

/-- The norms of complementary tails tend to zero. -/
theorem tendsto_norm_lpTail_zero (f : lp E 2) :
    Tendsto (fun s : Finset ι ↦ ‖lpTail s f‖) atTop (𝓝 0) := by
  simpa using (continuous_norm.tendsto 0).comp (tendsto_lpTail_zero f)

/-- Exact squared-norm formula for the complementary tail. -/
theorem norm_lpTail_sq (s : Finset ι) (f : lp E 2) :
    ‖lpTail s f‖ ^ 2 = ‖f‖ ^ 2 - ∑ i ∈ s, ‖f i‖ ^ 2 := by
  simpa [lpTail, lpHead] using
    (lp.norm_compl_sum_single (p := (2 : ENNReal)) (by norm_num) f s)

/-- Pythagorean decomposition into a finite coordinate head and its tail. -/
theorem norm_sq_eq_sum_add_norm_lpTail_sq (s : Finset ι) (f : lp E 2) :
    ‖f‖ ^ 2 = (∑ i ∈ s, ‖f i‖ ^ 2) + ‖lpTail s f‖ ^ 2 := by
  rw [norm_lpTail_sq]
  ring

/-- The global norm-square defect splits exactly into the finite sum of its
coordinate defects plus the defect of the complementary tails. -/
theorem normSqDefect_eq_sum_add_tail (s : Finset ι) (u v : lp E 2) :
    normSqDefect u v =
      (∑ i ∈ s, normSqDefect (u i) (v i)) +
        normSqDefect (lpTail s u) (lpTail s v) := by
  unfold normSqDefect
  rw [norm_sq_eq_sum_add_norm_lpTail_sq s (u + v),
    norm_sq_eq_sum_add_norm_lpTail_sq s u,
    norm_sq_eq_sum_add_norm_lpTail_sq s v, lpTail_add]
  simp only [lp.coeFn_add, Pi.add_apply, Finset.sum_sub_distrib]
  ring

/-- The universal defect estimate applied to two complementary tails. -/
theorem abs_normSqDefect_lpTail_le (s : Finset ι) (u v : lp E 2) :
    |normSqDefect (lpTail s u) (lpTail s v)| ≤
      2 * ‖lpTail s u‖ * ‖lpTail s v‖ :=
  abs_normSqDefect_le (lpTail s u) (lpTail s v)

/-- A uniformly bounded second vector makes the tail defect arbitrarily small
as the first vector's finite head exhausts its coordinates. -/
theorem tendsto_normSqDefect_lpTail_zero (u : lp E 2) {v : Finset ι → lp E 2}
    {C : ℝ} (hv : ∀ s, ‖lpTail s (v s)‖ ≤ C) :
    Tendsto (fun s ↦ normSqDefect (lpTail s u) (lpTail s (v s)))
      atTop (𝓝 0) := by
  have hnonneg : 0 ≤ C := by
    classical
    simpa using le_trans (norm_nonneg (lpTail ∅ (v ∅))) (hv ∅)
  have hbound : Tendsto (fun s : Finset ι ↦ (2 * C) * ‖lpTail s u‖)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_norm_lpTail_zero u)
  have hneg : Tendsto (fun s : Finset ι ↦ -((2 * C) * ‖lpTail s u‖))
      atTop (𝓝 0) := by
    simpa using hbound.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hbound
  · filter_upwards with s
    have habs : |normSqDefect (lpTail s u) (lpTail s (v s))| ≤
        (2 * C) * ‖lpTail s u‖ := by
      calc
        |normSqDefect (lpTail s u) (lpTail s (v s))| ≤
            2 * ‖lpTail s u‖ * ‖lpTail s (v s)‖ :=
          abs_normSqDefect_le (lpTail s u) (lpTail s (v s))
        _ ≤ 2 * ‖lpTail s u‖ * C :=
          mul_le_mul_of_nonneg_left (hv s) (by positivity)
        _ = (2 * C) * ‖lpTail s u‖ := by ring
    exact le_trans (neg_le_neg habs) (neg_abs_le _)
  · filter_upwards with s
    have habs : |normSqDefect (lpTail s u) (lpTail s (v s))| ≤
        (2 * C) * ‖lpTail s u‖ := by
      calc
        |normSqDefect (lpTail s u) (lpTail s (v s))| ≤
            2 * ‖lpTail s u‖ * ‖lpTail s (v s)‖ :=
          abs_normSqDefect_le (lpTail s u) (lpTail s (v s))
        _ ≤ 2 * ‖lpTail s u‖ * C :=
          mul_le_mul_of_nonneg_left (hv s) (by positivity)
        _ = (2 * C) * ‖lpTail s u‖ := by ring
    exact le_trans (le_abs_self _) habs

end L2Sum

end

end NormFormula
