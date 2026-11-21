import NormFormula.Analytic.BanachUltrapower
import NormFormula.ModelTheory.SeparableIPModel
import NormFormula.Examples.XYIPPattern
import NormFormula.Analytic.XPositiveIndex

/-! # Finite boxes give IP in every free Banach ultrapower -/
namespace NormFormula
noncomputable section
open Filter BanachUltrapower
open scoped Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- No choice of a particular free ultrafilter is needed. The rows and
parameters retain the original bounds and thresholds in the completed
Banach ultrapower. -/
theorem norm_hasInfiniteIPWitness_ultrapower_of_finitePatterns
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    {R S low high : ℝ}
    (hp : HasIPPatternsInEveryDimension (fun x y : E ↦ ‖x + y‖) R S low high) :
    HasBoundedInfiniteIPWitness
      (fun x y : BanachUltrapower U E ↦ ‖x + y‖) R S low high := by
  classical
  have hR : 0 ≤ R := by
    obtain ⟨r, hr, _⟩ := hp 1
    exact (norm_nonneg _).trans (hr 0)
  choose rows hrows patterns using fun n ↦ hp (n + 1)
  let row (i n : ℕ) : E := if hi : i < n + 1 then rows n ⟨i, hi⟩ else 0
  have hr (i n : ℕ) : ‖row i n‖ ≤ R := by
    dsimp [row]
    split_ifs
    · exact hrows _ _
    · simpa using hR
  let r (i : ℕ) := boundedFamily (row i) R (hr i)
  refine ⟨fun i ↦ ofBounded U (r i),
    fun i ↦ norm_ofBounded_le U _ (Eventually.of_forall (hr i)), ?_⟩
  intro A B hAB
  let subset (n : ℕ) : Finset (Fin (n + 1)) := Finset.univ.filter fun i ↦ i.val ∈ B
  choose parameter hhigh hlow using fun n ↦ patterns n (subset n)
  let p := boundedFamily (fun n ↦ (parameter n).1) S (fun n ↦ (parameter n).2)
  refine ⟨ofBounded U p, norm_ofBounded_le U _
    (Eventually.of_forall fun n ↦ (parameter n).2), ?_, ?_⟩
  · intro i hi
    dsimp only
    rw [← ofBounded_add]
    apply le_of_tendsto (tendsto_norm_ofBounded U (r i + p))
    filter_upwards [hU (eventually_ge_atTop i)] with n hn
    have hin : i < n + 1 := by omega
    have hiB : i ∉ B := Finset.disjoint_left.mp hAB hi
    change ‖row i n + (parameter n).1‖ ≤ low
    simpa [row, hin, hn, boundedBinaryValue] using
      hlow n ⟨i, hin⟩ (by simp [subset, hiB])
  · intro i hi
    dsimp only
    rw [← ofBounded_add]
    apply ge_of_tendsto (tendsto_norm_ofBounded U (r i + p))
    filter_upwards [hU (eventually_ge_atTop i)] with n hn
    have hin : i < n + 1 := by omega
    change high ≤ ‖row i n + (parameter n).1‖
    simpa [row, hin, hn, boundedBinaryValue] using
      hhigh n ⟨i, hin⟩ (by simp [subset, hi])

/-- Finite-box data transport along a linear isometry equivalence. -/
theorem HasIPPatternsInEveryDimension.of_norm_equiv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {R S low high : ℝ}
    (h : HasIPPatternsInEveryDimension (fun x y : F ↦ ‖x + y‖) R S low high) :
    HasIPPatternsInEveryDimension (fun x y : E ↦ ‖x + y‖) R S low high := by
  intro n
  obtain ⟨r, hr, hp⟩ := h n
  refine ⟨fun i ↦ e.symm (r i), fun i ↦ by simpa using hr i, ?_⟩
  intro A
  obtain ⟨p, hpA, hpAc⟩ := hp A
  refine ⟨⟨e.symm p.1, by simpa using p.2⟩, ?_, ?_⟩
  · intro i hi
    simpa [boundedBinaryValue, ← map_add] using hpA i hi
  · intro i hi
    simpa [boundedBinaryValue, ← map_add] using hpAc i hi

namespace X

theorem positive_norm_hasIPPatternsInEveryDimension :
    HasIPPatternsInEveryDimension (fun x y : XPositiveSpace ↦ ‖x + y‖)
      (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 6) :=
  HasIPPatternsInEveryDimension.of_norm_equiv xSpaceEquivPositive.symm
    normTranslate_hasIPPatternsInEveryDimension

theorem positive_norm_ultrapower_hasInfiniteIPWitness
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    HasBoundedInfiniteIPWitness
      (fun x y : BanachUltrapower U XPositiveSpace ↦ ‖x + y‖)
      (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 6) :=
  norm_hasInfiniteIPWitness_ultrapower_of_finitePatterns U hU
    positive_norm_hasIPPatternsInEveryDimension
end X
end
end NormFormula
