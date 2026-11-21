import NormFormula.ContinuousLogic.BanachBallFormulaLos
import NormFormula.ContinuousLogic.BanachBallTheoryIP

/-!
# Finite-pattern compactness in the typed ball language

Place a pattern of dimension `n + 1` in coordinate `n` of the completed ball
reduced product.  Every fixed row index and every finite disjoint low/high
request is then correct on an ultrafilter tail.  Full typed Łoś supplies the
same complete theory, while the atomic evaluation law passes those eventual
threshold inequalities to one infinite witness.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Filter

universe u w

namespace BallFormula

variable {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}

/-- The diagonal copy in the completed reduced product preserves every
formula on assignments from the original structure. -/
theorem realize_reducedConst
    (M : BallStructure.{u, w} Symbol symbolRadius)
    {n : ℕ} {context : BallContext n}
    (formula : BallFormula Symbol symbolRadius context)
    (assignment : BallTerm.Assignment M.toRationalBallSystem context) :
    formula.realize M.reducedProduct
        (fun i ↦ M.toRationalBallSystem.reducedConst (context i) (assignment i)) =
      formula.realize M assignment := by
  have h := realize_reducedProduct M formula (fun i _ ↦ assignment i)
  change formula.realize M.reducedProduct
      (fun i ↦ M.toRationalBallSystem.reducedConst (context i) (assignment i)) =
    ultralimit (fun _ : ℕ ↦ formula.realize M assignment) at h
  rwa [ultralimit_const] at h

/-- Binary formula evaluation on two completed sequence representatives is
the ultralimit of the coordinatewise binary evaluations. -/
@[simp]
theorem realize_binary_reducedProduct_mk
    {rowRadius parameterRadius : ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius)
    (formula : BallFormula Symbol symbolRadius
      (![rowRadius, parameterRadius] : BallContext 2))
    (rows : ReducedSequence (M.toRationalBallSystem.reducedBound rowRadius))
    (parameters : ReducedSequence
      (M.toRationalBallSystem.reducedBound parameterRadius)) :
    formula.realize M.reducedProduct
        (Fin.cons
          (ReducedProduct.completedMk
            (M.toRationalBallSystem.reducedBound rowRadius) rows)
          (Fin.cons
            (ReducedProduct.completedMk
              (M.toRationalBallSystem.reducedBound parameterRadius) parameters)
            (fun i : Fin 0 ↦ nomatch i))) =
      ultralimit fun k ↦ formula.realize M
        (Fin.cons (rows k) (Fin.cons (parameters k) (fun i : Fin 0 ↦ nomatch i))) := by
  let S := M.toRationalBallSystem
  let assignment : BallTerm.ReducedAssignment S
      (![rowRadius, parameterRadius] : BallContext 2) :=
    Fin.cons rows (Fin.cons parameters (fun i : Fin 0 ↦ nomatch i))
  have h := BallFormula.realize_reducedProduct M formula assignment
  have hcompleted : BallTerm.completedAssignment S assignment =
      Fin.cons
        (ReducedProduct.completedMk (S.reducedBound rowRadius) rows)
        (Fin.cons
          (ReducedProduct.completedMk (S.reducedBound parameterRadius) parameters)
          (fun i : Fin 0 ↦ nomatch i)) := by
    funext i
    fin_cases i <;> rfl
  rw [hcompleted] at h
  have hvalues :
      (fun k ↦ formula.realize M (BallTerm.coordinateAssignment S assignment k)) =
      (fun k ↦ formula.realize M
        (Fin.cons (rows k) (Fin.cons (parameters k) (fun i : Fin 0 ↦ nomatch i)))) := by
    funext k
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hvalues] at h
  exact h

/-- Finite fixed-gap patterns produce an infinite witness in the completed
reduced product of the original structure. -/
theorem hasInfiniteIPWitness_reducedProduct_of_finitePatterns
    {rowRadius parameterRadius : ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius)
    (formula : BallFormula Symbol symbolRadius
      (![rowRadius, parameterRadius] : BallContext 2))
    (low high : ℝ)
    (hpatterns : formula.HasFiniteIPPatternsInEveryDimension M low high) :
    formula.HasInfiniteIPWitness M.reducedProduct low high := by
  have hpatterns' : ∀ n : ℕ, ∃ rows : Fin (n + 1) → M.Ball rowRadius,
      NormFormula.IsIPPattern
        (fun i parameter ↦ formula.binaryValue M (rows i) parameter) low high :=
    fun n ↦ hpatterns (n + 1)
  choose finiteRows finitePattern using hpatterns'
  let defaultRow : M.Ball rowRadius := Classical.choice inferInstance
  let rowRepresentative (i : ℕ) :
      ReducedSequence (M.toRationalBallSystem.reducedBound rowRadius) := fun n ↦
    if hi : i < n + 1 then finiteRows n ⟨i, hi⟩ else defaultRow
  let productRows : ℕ → M.reducedProduct.Ball rowRadius := fun i ↦
    ReducedProduct.completedMk (M.toRationalBallSystem.reducedBound rowRadius)
      (rowRepresentative i)
  refine ⟨productRows, ?_⟩
  intro E F hdisjoint
  let highSubset (n : ℕ) : Finset (Fin (n + 1)) :=
    Finset.univ.filter fun i ↦ (i : ℕ) ∈ F
  have hparameters : ∀ n : ℕ, ∃ parameter : M.Ball parameterRadius,
      (∀ i ∈ highSubset n,
          high ≤ formula.binaryValue M (finiteRows n i) parameter) ∧
        (∀ i ∉ highSubset n,
          formula.binaryValue M (finiteRows n i) parameter ≤ low) :=
    fun n ↦ finitePattern n (highSubset n)
  choose parameter parameterPattern using hparameters
  let parameterRepresentative :
      ReducedSequence (M.toRationalBallSystem.reducedBound parameterRadius) := parameter
  refine ⟨ReducedProduct.completedMk
      (M.toRationalBallSystem.reducedBound parameterRadius) parameterRepresentative, ?_, ?_⟩
  · intro i hiE
    change (formula.realize M.reducedProduct
      (Fin.cons
        (ReducedProduct.completedMk (M.toRationalBallSystem.reducedBound rowRadius)
          (rowRepresentative i))
        (Fin.cons
          (ReducedProduct.completedMk
            (M.toRationalBallSystem.reducedBound parameterRadius)
            parameterRepresentative)
          (fun j : Fin 0 ↦ nomatch j))) : ℝ) ≤ low
    rw [realize_binary_reducedProduct_mk]
    apply ultralimit_coe_le_of_eventually_le
    filter_upwards [eventually_ge_indexUltrafilter i] with n hn
    have hin : i < n + 1 := Nat.lt_succ_of_le hn
    let index : Fin (n + 1) := ⟨i, hin⟩
    have hiNotF : i ∉ F := Finset.disjoint_left.mp hdisjoint hiE
    have hindex : index ∉ highSubset n := by
      simp [highSubset, index, hiNotF]
    have hlow := (parameterPattern n).2 index hindex
    simpa [BallFormula.binaryValue, rowRepresentative,
      parameterRepresentative, hn, hin, index] using hlow
  · intro i hiF
    change high ≤ (formula.realize M.reducedProduct
      (Fin.cons
        (ReducedProduct.completedMk (M.toRationalBallSystem.reducedBound rowRadius)
          (rowRepresentative i))
        (Fin.cons
          (ReducedProduct.completedMk
            (M.toRationalBallSystem.reducedBound parameterRadius)
            parameterRepresentative)
          (fun j : Fin 0 ↦ nomatch j))) : ℝ)
    rw [realize_binary_reducedProduct_mk]
    apply le_ultralimit_coe_of_eventually_le
    filter_upwards [eventually_ge_indexUltrafilter i] with n hn
    have hin : i < n + 1 := Nat.lt_succ_of_le hn
    let index : Fin (n + 1) := ⟨i, hin⟩
    have hindex : index ∈ highSubset n := by
      simp [highSubset, index, hiF]
    have hhigh := (parameterPattern n).1 index hindex
    simpa [BallFormula.binaryValue, rowRepresentative,
      parameterRepresentative, hn, hin, index] using hhigh

/-- The completed reduced product witnessing IP has the original complete theory. -/
theorem exists_sameTheory_infiniteWitness_of_finitePatterns
    {rowRadius parameterRadius : ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius)
    (formula : BallFormula Symbol symbolRadius
      (![rowRadius, parameterRadius] : BallContext 2))
    (low high : ℝ)
    (hpatterns : formula.HasFiniteIPPatternsInEveryDimension M low high) :
    ∃ N : BallStructure.{u, w} Symbol symbolRadius,
      BallSameCompleteTheory M N ∧ formula.HasInfiniteIPWitness N low high :=
  ⟨M.reducedProduct, ballSameCompleteTheory_reducedProduct M,
    hasInfiniteIPWitness_reducedProduct_of_finitePatterns M formula low high hpatterns⟩

/-- Every typed ball structure satisfies the finite-pattern compactness
principle, witnessed by its completed reduced product. -/
theorem finitePatternCompactness
    (M : BallStructure.{u, w} Symbol symbolRadius) :
    FinitePatternCompactness M := by
  intro rowRadius parameterRadius formula low high hgap hpatterns
  obtain ⟨N, hTheory, hWitness⟩ :=
    exists_sameTheory_infiniteWitness_of_finitePatterns
      M formula low high hpatterns
  exact ⟨N, hTheory, low, high, hgap, hWitness⟩

end BallFormula

end


end NormFormula.ContinuousLogic
