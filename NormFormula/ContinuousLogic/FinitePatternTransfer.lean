import NormFormula.Combinatorics.FiniteIPPattern
import NormFormula.ContinuousLogic.FiniteDiagramFamily
import NormFormula.ContinuousLogic.MultiTheoryIP

/-!
# Finite-pattern transfer in a complete continuous theory

An infinite fixed-gap IP witness in a same-theory model yields finite patterns
of every dimension in the home model, after shrinking the gap by an arbitrary
positive approximation tolerance.  Finite elementary-diagram
satisfiability supplies the transfer simultaneously for all rows and all
subset parameters in one finite pattern.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u v w

attribute [local instance] MultiStructure.rowNonempty
  MultiStructure.parameterNonempty

namespace MultiFormula

/-- Fixed-gap finite IP patterns for a formula in every dimension of one
bounded structure. -/
def HasFiniteIPPatternsInEveryDimension {Symbol : Type w}
    (M : MultiStructure.{u, v, w} Symbol)
    (φ : MultiFormula Symbol 1 1) (low high : ℝ) : Prop :=
  ∀ n : ℕ, ∃ rows : Fin n → M.Row,
    NormFormula.IsIPPattern
      (fun i parameter ↦ φ.binaryValue M (rows i) parameter) low high

/-- Transfer an infinite witness from a same-theory model to finite patterns
in the home model.  Approximation by `δ` changes the thresholds from
`low, high` to `low + δ, high - δ`. -/
theorem hasFiniteIPPatternsInEveryDimension_of_sameTheory_infiniteWitness
    {Symbol : Type w}
    {M N : MultiStructure.{u, v, w} Symbol}
    (hTheory : MultiSameCompleteTheory M N)
    (φ : MultiFormula Symbol 1 1) {low high δ : ℝ} (hδ : 0 < δ)
    (hwitness : HasInfiniteIPWitness N φ low high) :
    HasFiniteIPPatternsInEveryDimension M φ (low + δ) (high - δ) := by
  classical
  obtain ⟨allRows, hwitness⟩ := hwitness
  intro n
  have hparameter : ∀ S : Finset (Fin n), ∃ parameter : N.Parameter,
      (∀ i ∈ S, high ≤ φ.binaryValue N (allRows i) parameter) ∧
      (∀ i ∉ S, φ.binaryValue N (allRows i) parameter ≤ low) := by
    intro S
    let embedding : Fin n ↪ ℕ := Fin.valEmbedding
    let lowSet : Finset ℕ := (Finset.univ \ S).map embedding
    let highSet : Finset ℕ := S.map embedding
    have hdisjoint : Disjoint lowSet highSet := by
      exact (Finset.disjoint_map embedding).2 Finset.sdiff_disjoint
    obtain ⟨parameter, hlow, hhigh⟩ :=
      hwitness lowSet highSet hdisjoint
    refine ⟨parameter, ?_, ?_⟩
    · intro i hi
      apply hhigh i
      exact Finset.mem_map.mpr ⟨i, hi, rfl⟩
    · intro i hi
      apply hlow i
      exact Finset.mem_map.mpr
        ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
  choose parameters hparameters using hparameter
  let condition (pair : Fin n × Finset (Fin n)) :
      NamedDiagramCondition N :=
    { rowVars := 1
      parameterVars := 1
      formula := φ
      rows := fun _ ↦ allRows pair.1
      parameters := fun _ ↦ parameters pair.2 }
  let conditions : Finset (NamedDiagramCondition N) :=
    Finset.univ.image condition
  have hfinite : ∀ (fragment : FiniteElementaryDiagramFragment N) (ε : ℝ),
      0 < ε →
        ∃ rows : Fin fragment.rowVars → M.Row,
          ∃ parameters : Fin fragment.parameterVars → M.Parameter,
            ∀ i : Fin fragment.conditionCount,
              |(((fragment.formulas i).realize M rows parameters : ℝ) -
                (fragment.targets i : ℝ))| < ε := by
    intro fragment ε hε
    exact fragment.approximately_realized_of_sameCompleteTheory
      hTheory ε hε
  obtain ⟨realization⟩ := exists_finiteNamedDiagramRealization
    id M N (by simpa using hfinite) conditions δ hδ
  refine ⟨fun i ↦ realization.rows (allRows i), ?_⟩
  intro S
  refine ⟨realization.parameters (parameters S), ?_, ?_⟩
  · intro i hi
    have hcondition : condition (i, S) ∈ conditions := by
      exact Finset.mem_image.mpr ⟨(i, S), Finset.mem_univ _, rfl⟩
    have happrox := realization.realizes (condition (i, S)) hcondition
    have habs :
        |φ.binaryValue M (realization.rows (allRows i))
            (realization.parameters (parameters S)) -
          φ.binaryValue N (allRows i) (parameters S)| < δ := by
      simpa [condition, NamedDiagramCondition.target, Real.dist_eq,
        MultiFormula.binaryValue] using happrox
    have hhigh := (hparameters S).1 i hi
    linarith [abs_lt.mp habs |>.1]
  · intro i hi
    have hcondition : condition (i, S) ∈ conditions := by
      exact Finset.mem_image.mpr ⟨(i, S), Finset.mem_univ _, rfl⟩
    have happrox := realization.realizes (condition (i, S)) hcondition
    have habs :
        |φ.binaryValue M (realization.rows (allRows i))
            (realization.parameters (parameters S)) -
          φ.binaryValue N (allRows i) (parameters S)| < δ := by
      simpa [condition, NamedDiagramCondition.target, Real.dist_eq,
        MultiFormula.binaryValue] using happrox
    have hlow := (hparameters S).2 i hi
    linarith [abs_lt.mp habs |>.2]

/-- Theory-level IP forces some positive-gap finite pattern in every
dimension of the home structure. -/
theorem exists_finiteIPPatterns_of_hasIPInCompleteTheory
    {Symbol : Type w} {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1}
    (hIP : HasIPInCompleteTheory M φ) :
    ∃ low high : ℝ, low < high ∧
      HasFiniteIPPatternsInEveryDimension M φ low high := by
  obtain ⟨N, hTheory, low, high, hgap, hwitness⟩ := hIP
  let δ : ℝ := (high - low) / 4
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  refine ⟨low + δ, high - δ, by dsimp [δ]; linarith, ?_⟩
  exact hasFiniteIPPatternsInEveryDimension_of_sameTheory_infiniteWitness
    hTheory φ hδ hwitness

/-- A home-structure prohibition on fixed-gap finite patterns proves NIP in
the complete theory. -/
theorem isNIPInCompleteTheory_of_no_finiteIPPatterns
    {Symbol : Type w} {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1}
    (hno : ∀ low high : ℝ, low < high →
      ¬ HasFiniteIPPatternsInEveryDimension M φ low high) :
    IsNIPInCompleteTheory M φ := by
  intro hIP
  obtain ⟨low, high, hgap, hpatterns⟩ :=
    exists_finiteIPPatterns_of_hasIPInCompleteTheory hIP
  exact hno low high hgap hpatterns

end MultiFormula

end

end NormFormula.ContinuousLogic
