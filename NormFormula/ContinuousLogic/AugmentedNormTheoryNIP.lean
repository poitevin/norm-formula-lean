import NormFormula.Analytic.SeminormRenorm
import NormFormula.ContinuousLogic.HilbertSparseNIP
import NormFormula.ContinuousLogic.EuclideanConnective

/-! # The quadratic Hilbert--seminorm proposition -/
namespace NormFormula.ContinuousLogic
noncomputable section
universe u
variable {E H : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem quadratic_norm_reconstruction
    (e : E →ₗ[ℝ] H) (he : ∀ x, ‖e x‖ ≤ ‖x‖)
    (p : Seminorm ℝ E) (hp : ∀ x, p x ≤ ‖x‖)
    (hsq : ∀ x, ‖x‖ ^ 2 = ‖e x‖ ^ 2 + p x ^ 2)
    (R : ℝ) (hR : 0 < R) (x y : PositiveNormBall E R) :
    normAddTruth R hR x y = boundedEuclideanConnective ![
      seminormAddTruth ((normSeminorm ℝ H).comp e) he R hR x y,
      seminormAddTruth p hp R hR x y] := by
  apply Subtype.ext
  change ‖x.1+y.1‖ / (2*R) = min 1 (Real.sqrt
    ((‖e (x.1+y.1)‖ / (2*R))^2 + (p (x.1+y.1) / (2*R))^2))
  have hdenom : 0 < 2*R := by positivity
  have hid : (‖e (x.1+y.1)‖ / (2*R))^2 + (p (x.1+y.1) / (2*R))^2 =
      ‖x.1+y.1‖^2 / (2*R)^2 := by rw [hsq]; field_simp
  rw [hid, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hdenom.le]
  exact (min_eq_right (normAddTruth R hR x y).2.2).symm

/-- A quadratic norm decomposition with finite seminorm patterns gives
complete-theory NIP through Hilbert stability and connective closure. -/
theorem quadratic_norm_isBoundedLocalNIP
    (e : E →ₗ[ℝ] H) (he : ∀ x, ‖e x‖ ≤ ‖x‖)
    (p : Seminorm ℝ E) (hp : ∀ x, p x ≤ ‖x‖)
    (hsq : ∀ x, ‖x‖ ^ 2 = ‖e x‖ ^ 2 + p x ^ 2)
    (hlocal : IsBoundedLocalNIP (fun x y ↦ p (x+y))) :
    IsBoundedLocalNIP (fun x y : E ↦ ‖x+y‖) :=
  hilbert_sparse_norm_isBoundedLocalNIP e he p hp hlocal boundedEuclideanConnective
    (quadratic_norm_reconstruction e he p hp hsq)

/-- The paper's fat-shattering hypothesis, stated on independently bounded
Hilbert balls, implies the common-threshold finite-pattern hypothesis. -/
theorem boundedLocalNIP_of_finiteFat
    {K : Type*} [NormedAddCommGroup K] (p : K → ℝ)
    (hfat : ∀ R S ε : ℝ, 0 ≤ R → 0 ≤ S → 0 < ε →
      ∃ N : ℕ, ∀ (n : ℕ) (rows : Fin n → K), (∀ i, ‖rows i‖ ≤ R) →
        IsFatShattered (fun i (y : ClosedNormBall K S) ↦ p (rows i+y.1)) ε → n < N) :
    IsBoundedLocalNIP (fun x y ↦ p (x+y)) := by
  intro R S low high hgap
  obtain ⟨N, hN⟩ := hfat |R| |S| ((high-low)/2) (abs_nonneg _) (abs_nonneg _) (by linarith)
  refine ⟨N, ?_⟩
  intro n rows hrows hip
  apply hN n rows (fun i ↦ (hrows i).trans (le_abs_self R))
  apply IsIPPattern.isFatShattered_halfGap
  intro A
  obtain ⟨y, hhi, hlo⟩ := hip A
  exact ⟨⟨y.1, y.2.trans (le_abs_self S)⟩, hhi, hlo⟩

/-- `prop:hilbert-sparse-nip`, for the actual quadratic normed carrier.
The upper bound ensures the usual Banach/Hilbert norm equivalence; the NIP
argument only needs the lower comparisons inherent in the quadratic norm. -/
theorem augmentedSpace_fullTheoryNIP [CompleteSpace H]
    (p : Seminorm ℝ H) (C : ℝ) (hC : 0 ≤ C) (hp : ∀ x, p x ≤ C*‖x‖)
    (hfat : ∀ R S ε : ℝ, 0 ≤ R → 0 ≤ S → 0 < ε →
      ∃ N : ℕ, ∀ (n : ℕ) (rows : Fin n → H), (∀ i, ‖rows i‖ ≤ R) →
        IsFatShattered (fun i (y : ClosedNormBall H S) ↦ p (rows i+y.1)) ε → n < N)
    (rowRadius parameterRadius : ℚ≥0) :
    letI : CompleteSpace (AugmentedSpace p) := SeminormRenorm.completeSpace _ _
      (Real.sqrt (1+C^2)) (AugmentedSpace.upper p hC hp)
    (predicateFreeNormAddFormula rowRadius parameterRadius).IsNIPInCompleteTheory
      (standardBanachBallStructure (AugmentedSpace p)) := by
  letI : CompleteSpace (AugmentedSpace p) := SeminormRenorm.completeSpace _ _
    (Real.sqrt (1+C^2)) (AugmentedSpace.upper p hC hp)
  let e := (AugmentedSpace.linearEquiv p).toLinearMap
  let q := p.comp e
  have hlocal : IsBoundedLocalNIP (fun x y : AugmentedSpace p ↦ q (x+y)) := by
    simpa [q, e, ← map_add] using
      (boundedLocalNIP_of_finiteFat p hfat).comap e e
        (AugmentedSpace.hilbert_le p) (AugmentedSpace.hilbert_le p)
  exact hilbert_sparse_norm_fullTheoryNIP e (AugmentedSpace.hilbert_le p) q
    (AugmentedSpace.seminorm_le p) hlocal boundedEuclideanConnective
    (quadratic_norm_reconstruction e (AugmentedSpace.hilbert_le p) q
      (AugmentedSpace.seminorm_le p) (fun x ↦ augmentedNorm_sq p x.val))
    rowRadius parameterRadius
end
end NormFormula.ContinuousLogic
