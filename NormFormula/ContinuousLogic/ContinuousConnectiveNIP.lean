import NormFormula.ContinuousLogic.LocalTypeNIP

/-! # NIP under arbitrary finite continuous connectives

Take successive subsequences for the finitely many factor type spaces.
Continuity gives convergence on their compact product; an independent
sequence of continuous functions on that product would contradict it.
No Lipschitz bound on the connective is required.
-/

namespace NormFormula.ContinuousLogic
noncomputable section
open Filter
open scoped Topology

namespace MultiFormula

theorem simultaneous_pointwise_subsequence
    {ι X : Type*} {P : ι → Type*} (value : ∀ i, X → P i → ℝ)
    (h : ∀ i, ∀ rows : ℕ → X,
      HasPointwiseConvergentSubsequence (fun n ↦ value i (rows n)))
    (s : Finset ι) (rows : ℕ → X) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i ∈ s, ∀ p : P i, ∃ a : ℝ,
      Tendsto (fun n ↦ value i (rows (φ n)) p) atTop (𝓝 a) := by
  classical
  induction s using Finset.induction_on generalizing rows with
  | empty => exact ⟨id, strictMono_id, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨φ, hφ, hconv⟩ := ih rows
    obtain ⟨ψ, hψ, hnew⟩ := h i (rows ∘ φ)
    refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
    intro j hj p
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hnew p
    · obtain ⟨a, ha⟩ := hconv j hj p
      exact ⟨a, ha.comp hψ.tendsto_atTop⟩

/-- Every finite continuous connective preserves NIP on one structure. -/
theorem isNIPOnStructure_connective
    {Symbol : Type*} {M : MultiStructure Symbol} {d : ℕ}
    (gate : Connective d) (formulas : Fin d → MultiFormula Symbol 1 1)
    (hNIP : ∀ j, IsNIPOnStructure M (formulas j)) :
    IsNIPOnStructure M (.connective gate formulas) := by
  classical
  rintro ⟨low, high, hgap, rows, hrows⟩
  let P := ∀ j, LocalParameterType M (formulas j)
  let value : ℕ → P → ℝ := fun n p ↦
    (gate (fun j ↦ localTypeTruthValue (rows n) (p j)) : ℝ)
  have hindependent : HasIndependentSequence value := by
    refine ⟨low, high, hgap, ?_⟩
    intro A B hAB
    obtain ⟨y, hyA, hyB⟩ := hrows A B hAB
    refine ⟨fun j ↦ homeParameterType M (formulas j) y, ?_, ?_⟩
    · intro i hi
      exact hyA i hi
    · intro i hi
      exact hyB i hi
  have hcontinuous : ∀ n, Continuous (value n) := by
    intro n
    exact continuous_subtype_val.comp (gate.continuous_toFun.comp
      (continuous_pi fun j ↦ (continuous_localTypeTruthValue (rows n)).comp
        (continuous_apply j)))
  obtain ⟨φ, hφ, hconv⟩ := simultaneous_pointwise_subsequence
    (fun j row p ↦ localTypeValue (φ := formulas j) row p)
    (fun j ↦ isNIPOnStructure_iff_pointwiseConvergentSubsequenceOnLocalType_general.mp
      (hNIP j)) Finset.univ rows
  apply hindependent.no_pointwiseConvergence_along hcontinuous φ hφ
  intro p
  choose a ha using fun j ↦ hconv j (Finset.mem_univ j) (p j)
  have hmem (j : Fin d) : a j ∈ Set.Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto (ha j)
      (Eventually.of_forall fun n ↦ (localTypeTruthValue (rows (φ n)) (p j)).2)
  let limits : Fin d → TruthValue := fun j ↦ ⟨a j, hmem j⟩
  have hvalues : Tendsto
      (fun n j ↦ localTypeTruthValue (rows (φ n)) (p j)) atTop (𝓝 limits) := by
    apply tendsto_pi_nhds.mpr
    intro j
    exact tendsto_subtype_rng.mpr (ha j)
  exact ⟨gate limits, (continuous_subtype_val.tendsto _).comp
    ((gate.continuous_toFun.tendsto limits).comp hvalues)⟩

/-- The complete-theory closure lemma for arbitrary finite continuous
connectives, after the usual normalization of compact intervals to `[0,1]`. -/
theorem isNIPInCompleteTheory_connective
    {Symbol : Type*} {M : MultiStructure Symbol} {d : ℕ}
    (gate : Connective d) (formulas : Fin d → MultiFormula Symbol 1 1)
    (hNIP : ∀ j, IsNIPInCompleteTheory M (formulas j)) :
    IsNIPInCompleteTheory M (.connective gate formulas) := by
  rintro ⟨N, hTheory, hIP⟩
  apply isNIPOnStructure_connective gate formulas (M := N) ?_ hIP
  intro j hj
  exact hNIP j ⟨N, hTheory, hj⟩

end MultiFormula
end
end NormFormula.ContinuousLogic
