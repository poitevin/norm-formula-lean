import NormFormula.Analytic.L2SumStability
import NormFormula.Analytic.C0
import NormFormula.ModelTheory.UltrapowerIP
import NormFormula.ContinuousLogic.FullBanachBallTheoryIP

/-! # The stable sum of finite-dimensional sup-norm spaces -/
namespace NormFormula.XInfinity
noncomputable section
open Filter BanachUltrapower
open scoped Topology ENNReal

/-- Positive-index sum `(⊕ ℓ∞ⁿ)₂`. -/
abbrev Space := lp (fun n : ℕ ↦ Fin (n+1) → ℝ) 2

theorem norm_stable : IsStableOnBounded (fun x y : Space ↦ ‖x+y‖) :=
  l2Sum_norm_isStableOnBounded

/-- The finite truncation of a bounded sequence in the `n`th block. -/
def truncation (x : BoundedScalarSequences) (n : ℕ) : Space :=
  lp.single 2 n (fun i : Fin (n+1) ↦ x i)

theorem norm_truncation_le (x : BoundedScalarSequences) (n : ℕ) :
    ‖truncation x n‖ ≤ ‖x‖ := by
  rw [truncation, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun i ↦
    lp.norm_apply_le_norm ENNReal.top_ne_zero x i

theorem norm_coord_le_truncation (x : BoundedScalarSequences) {i n : ℕ} (hi : i ≤ n) :
    ‖x i‖ ≤ ‖truncation x n‖ := by
  rw [truncation, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  exact norm_le_pi_norm (fun j : Fin (n+1) ↦ x j) ⟨i, by omega⟩

def truncationFamily (x : BoundedScalarSequences) : lp (fun _ : ℕ ↦ Space) ∞ :=
  boundedFamily (truncation x) ‖x‖ (norm_truncation_le x)

/-- The displayed map into every free ultrapower is actually an isometry
on all bounded scalar sequences, hence in particular on `c₀`. -/
def boundedSequencesEmbedding (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    BoundedScalarSequences →ₗᵢ[ℝ] BanachUltrapower U Space where
  toFun x := ofBounded U (truncationFamily x)
  map_add' x y := by
    rw [← ofBounded_add]
    congr 1
    apply lp.ext
    funext n
    exact lp.single_add _ _ _ _
  map_smul' r x := by
    rw [← ofBounded_smul]
    congr 1
    apply lp.ext
    funext n
    change lp.single (E := fun n : ℕ ↦ Fin (n+1) → ℝ) 2 n (r • (fun i : Fin (n+1) ↦ x i)) =
      r • lp.single (E := fun n : ℕ ↦ Fin (n+1) → ℝ) 2 n (fun i : Fin (n+1) ↦ x i)
    exact lp.single_smul 2 n r _
  norm_map' x := by
    apply le_antisymm
    · exact norm_ofBounded_le U _ (Eventually.of_forall (norm_truncation_le x))
    · apply lp.norm_le_of_forall_le (norm_nonneg _)
      intro i
      apply ge_of_tendsto (tendsto_norm_ofBounded U (truncationFamily x))
      filter_upwards [hU (eventually_ge_atTop i)] with n hn
      exact norm_coord_le_truncation x hn

/-- Isometric `c₀` embedding into every nonprincipal ultrapower. -/
def c0Embedding (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    C0Space →ₗᵢ[ℝ] BanachUltrapower U Space :=
  (boundedSequencesEmbedding U hU).comp (Submodule.subtypeₗᵢ c0Submodule)

/-- The rows are coordinate unit vectors in one finite block. -/
def row {n : ℕ} (i : Fin n) : Space :=
  lp.single 2 n (Pi.single (Fin.castSucc i) 1)

/-- A subset parameter is its characteristic function in the same block. -/
def parameter {n : ℕ} (A : Finset (Fin n)) : Space :=
  lp.single 2 n (fun j : Fin (n+1) ↦ if j ∈ A.image Fin.castSucc then 1 else 0)

theorem row_norm_le {n : ℕ} (i : Fin n) : ‖row i‖ ≤ 1 := by
  rw [row, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro j
  by_cases h : j = Fin.castSucc i <;> simp [Pi.single_apply, h]

theorem parameter_norm_le {n : ℕ} (A : Finset (Fin n)) : ‖parameter A‖ ≤ 1 := by
  rw [parameter, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro j
  split_ifs <;> norm_num

theorem row_add_parameter {n : ℕ} (i : Fin n) (A : Finset (Fin n)) :
    ‖row i + parameter A‖ = if i ∈ A then 2 else 1 := by
  classical
  rw [row, parameter, ← lp.single_add, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  have hi : Fin.castSucc i ∈ A.image Fin.castSucc ↔ i ∈ A := by simp
  by_cases h : i ∈ A
  · rw [if_pos h]
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 2)).mpr
      intro j
      change ‖(Pi.single (Fin.castSucc i) (1:ℝ) : Fin (n+1) → ℝ) j +
        (if j ∈ A.image Fin.castSucc then 1 else 0)‖ ≤ 2
      by_cases hj : j = Fin.castSucc i <;> simp [Pi.single_apply, hj, hi, h]
      all_goals (try split_ifs) <;> norm_num
    · convert norm_le_pi_norm
        ((Pi.single (Fin.castSucc i) (1:ℝ) : Fin (n+1) → ℝ) + fun j ↦ if j ∈ A.image Fin.castSucc then 1 else 0)
        (Fin.castSucc i) using 1; norm_num [h]
  · rw [if_neg h]
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
      intro j
      change ‖(Pi.single (Fin.castSucc i) (1:ℝ) : Fin (n+1) → ℝ) j +
        (if j ∈ A.image Fin.castSucc then 1 else 0)‖ ≤ 1
      by_cases hj : j = Fin.castSucc i <;> simp [Pi.single_apply, hj, hi, h]
      all_goals (try split_ifs) <;> norm_num
    · convert norm_le_pi_norm
        ((Pi.single (Fin.castSucc i) (1:ℝ) : Fin (n+1) → ℝ) + fun j ↦ if j ∈ A.image Fin.castSucc then 1 else 0)
        (Fin.castSucc i) using 1; norm_num [h]

theorem finite_boxes : HasIPPatternsInEveryDimension
    (fun x y : Space ↦ ‖x+y‖) 1 1 1 2 := by
  intro n
  refine ⟨row, row_norm_le, ?_⟩
  intro A
  refine ⟨⟨parameter A, parameter_norm_le A⟩, ?_, ?_⟩
  · intro i hi
    change 2 ≤ ‖row i + parameter A‖
    simp [row_add_parameter, hi]
  · intro i hi
    change ‖row i + parameter A‖ ≤ 1
    simp [row_add_parameter, hi]

theorem ultrapower_IP (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    HasBoundedInfiniteIPWitness (fun x y : BanachUltrapower U Space ↦ ‖x+y‖) 1 1 1 2 :=
  norm_hasInfiniteIPWitness_ultrapower_of_finitePatterns U hU finite_boxes

open ContinuousLogic

/-- The `1,2` boxes on unit balls, in the full Banach language. Its output
sort has metric bound `4`, so the normalized thresholds are `1/4,1/2`. -/
theorem predicateFreeNormAddFormula_hasFiniteIPPatternsInEveryDimension :
    (predicateFreeNormAddFormula 1 1).HasFiniteIPPatternsInEveryDimension
      (standardBanachBallStructure Space) (1/4) (1/2) := by
  intro n
  let rows : Fin n → (standardBanachBallStructure Space).Ball 1 :=
    fun i ↦ ⟨row i, by simpa using row_norm_le i⟩
  refine ⟨rows, ?_⟩
  intro A
  let y : (standardBanachBallStructure Space).Ball 1 :=
    ⟨parameter A, by simpa using parameter_norm_le A⟩
  refine ⟨y, ?_, ?_⟩
  · intro i hi
    change (1/2 : ℝ) ≤ (predicateFreeNormAddFormula 1 1).binaryValue _ (rows i) y
    rw [BallFormula.binaryValue, predicateFreeNormAddFormula_value]
    change (1/2 : ℝ) ≤ ‖row i + parameter A‖ / rationalBallMetricBound (1+1)
    rw [row_add_parameter, if_pos hi]
    norm_num [rationalBallMetricBound]
  · intro i hi
    change (predicateFreeNormAddFormula 1 1).binaryValue _ (rows i) y ≤ (1/4 : ℝ)
    rw [BallFormula.binaryValue, predicateFreeNormAddFormula_value]
    change ‖row i + parameter A‖ / rationalBallMetricBound (1+1) ≤ (1/4 : ℝ)
    rw [row_add_parameter, if_neg hi]
    norm_num [rationalBallMetricBound]

/-- Section 3.3's complete-theory conclusion, obtained directly from the
finite boxes by compactness in the full standard Banach ball language. -/
theorem predicateFreeNormAddFormula_hasIPInCompleteTheory :
    (predicateFreeNormAddFormula 1 1).HasIPInCompleteTheory
      (standardBanachBallStructure Space) :=
  BallFormula.finitePatternCompactness (standardBanachBallStructure Space)
    (predicateFreeNormAddFormula 1 1) (1/4) (1/2) (by norm_num)
    predicateFreeNormAddFormula_hasFiniteIPPatternsInEveryDimension
end
end NormFormula.XInfinity
