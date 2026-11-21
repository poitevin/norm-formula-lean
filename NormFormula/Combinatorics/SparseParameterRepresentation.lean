import NormFormula.Combinatorics.PolynomialSparseTrace

/-!
# Enumerating an unlabelled sparse parameter

Finite supports in the two copies of `ℓ₂` are enumerated by one finite label
type.  Each label records its copy, numerical index, and amplitude.  The
resulting labelled affine coordinate forms reconstruct the original sparse
parameter exactly.  This supplies the bridge from the labelled sparse trace
bound to the vector-valued statement in the manuscript.
-/

namespace NormFormula.HalfGraph

/-- A coordinate in one of two prescribed finite supports. -/
abbrev SparsePairCoordinate (A B : Finset ℕ) := (A : Type) ⊕ (B : Type)

/-- Number of labelled coordinates used to enumerate the two supports. -/
abbrev sparsePairLabelCount (A B : Finset ℕ) :=
  Fintype.card (SparsePairCoordinate A B)

/-- A canonical enumeration of the two support subtypes. -/
noncomputable def sparsePairLabelEquiv (A B : Finset ℕ) :
    SparsePairCoordinate A B ≃ Fin (sparsePairLabelCount A B) :=
  Fintype.equivFin _

/-- Copy occupied by an enumerated support coordinate. -/
noncomputable def sparsePairCopy (A B : Finset ℕ) :
    Fin (sparsePairLabelCount A B) → CoordinateCopy :=
  fun a ↦ match (sparsePairLabelEquiv A B).symm a with
    | Sum.inl _ => .first
    | Sum.inr _ => .second

/-- Numerical index of an enumerated support coordinate. -/
noncomputable def sparsePairIndex (A B : Finset ℕ) :
    Fin (sparsePairLabelCount A B) → ℕ :=
  fun a ↦ match (sparsePairLabelEquiv A B).symm a with
    | Sum.inl i => i.1
    | Sum.inr j => j.1

/-- Amplitude attached to an enumerated support coordinate. -/
noncomputable def sparsePairAmplitude (u v : RealL2) (A B : Finset ℕ) :
    Fin (sparsePairLabelCount A B) → ℝ :=
  fun a ↦ match (sparsePairLabelEquiv A B).symm a with
    | Sum.inl i => u i.1
    | Sum.inr j => v j.1

@[simp]
theorem sparsePairLabelCount_eq (A B : Finset ℕ) :
    sparsePairLabelCount A B = A.card + B.card := by
  simp [sparsePairLabelCount, SparsePairCoordinate]

/-- A sum over a finite support subtype selects the requested coordinate when
it belongs to that support. -/
theorem sum_supportSubtype_ite (A : Finset ℕ) (w : ℕ → ℝ) (n : ℕ) :
    (∑ a : A, if a.1 = n then w a.1 else 0) = if n ∈ A then w n else 0 := by
  classical
  by_cases hn : n ∈ A
  · rw [if_pos hn]
    have heq : ∀ a : A, (a.1 = n ↔ a = ⟨n, hn⟩) := by
      intro a
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h
    simp only [heq]
    simp
  · rw [if_neg hn]
    have hne : ∀ a : A, a.1 ≠ n := by
      intro a h
      apply hn
      simpa [h] using a.2
    simp [hne]

/-- The first-copy labelled amplitudes sum to the original first coordinate. -/
theorem sparsePair_first_amplitude_sum (u v : RealL2) (A B : Finset ℕ) (n : ℕ) :
    (∑ a, if sparsePairCopy A B a = .first ∧ sparsePairIndex A B a = n then
        sparsePairAmplitude u v A B a else 0) =
      if n ∈ A then u n else 0 := by
  classical
  rw [← (sparsePairLabelEquiv A B).sum_comp]
  rw [Fintype.sum_sum_type]
  simp only [sparsePairCopy, sparsePairIndex, sparsePairAmplitude,
    Equiv.symm_apply_apply, true_and,
    reduceCtorEq, false_and, if_false, Finset.sum_const_zero, add_zero]
  exact sum_supportSubtype_ite A (fun i ↦ u i) n

/-- The second-copy labelled amplitudes sum to the original second
coordinate. -/
theorem sparsePair_second_amplitude_sum (u v : RealL2) (A B : Finset ℕ) (n : ℕ) :
    (∑ a, if sparsePairCopy A B a = .second ∧ sparsePairIndex A B a = n then
        sparsePairAmplitude u v A B a else 0) =
      if n ∈ B then v n else 0 := by
  classical
  rw [← (sparsePairLabelEquiv A B).sum_comp]
  rw [Fintype.sum_sum_type]
  simp only [sparsePairCopy, sparsePairIndex, sparsePairAmplitude,
    Equiv.symm_apply_apply, reduceCtorEq,
    false_and, if_false, Finset.sum_const_zero, zero_add, true_and]
  exact sum_supportSubtype_ite B (fun i ↦ v i) n

/-- Evaluation of a first-copy labelled coordinate form adds exactly the
corresponding sparse parameter coordinate. -/
theorem labelledCoordinateForm_eval_sparsePair_first
    (row : ℕ → ℝ) (u v : RealL2) (A B : Finset ℕ)
    (hU : ∀ n, n ∉ A → u n = 0) (n : ℕ) :
    (labelledCoordinateForm row (sparsePairCopy A B) (sparsePairIndex A B)
      .first n).eval (sparsePairAmplitude u v A B) = row n + u n := by
  rw [labelledCoordinateForm_eval, sparsePair_first_amplitude_sum]
  by_cases hn : n ∈ A
  · simp [hn]
  · simp [hn, hU n hn]

/-- Evaluation of a second-copy labelled coordinate form adds exactly the
corresponding sparse parameter coordinate. -/
theorem labelledCoordinateForm_eval_sparsePair_second
    (row : ℕ → ℝ) (u v : RealL2) (A B : Finset ℕ)
    (hV : ∀ n, n ∉ B → v n = 0) (n : ℕ) :
    (labelledCoordinateForm row (sparsePairCopy A B) (sparsePairIndex A B)
      .second n).eval (sparsePairAmplitude u v A B) = row n + v n := by
  rw [labelledCoordinateForm_eval, sparsePair_second_amplitude_sum]
  by_cases hn : n ∈ B
  · simp [hn]
  · simp [hn, hV n hn]

/-- Every pair of finitely supported sequences has a labelled sparse
representation whose label count is the sum of the two support sizes. -/
theorem exists_labelled_sparse_parameter_representation
    (u v : RealL2) (A B : Finset ℕ)
    (hU : ∀ n, n ∉ A → u n = 0)
    (hV : ∀ n, n ∉ B → v n = 0) :
    ∃ (ℓ : ℕ) (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
        (t : Fin ℓ → ℝ),
      ℓ = A.card + B.card ∧
      (∀ row n, (labelledCoordinateForm row copy index .first n).eval t =
        row n + u n) ∧
      (∀ row n, (labelledCoordinateForm row copy index .second n).eval t =
        row n + v n) := by
  refine ⟨sparsePairLabelCount A B, sparsePairCopy A B, sparsePairIndex A B,
    sparsePairAmplitude u v A B, sparsePairLabelCount_eq A B, ?_, ?_⟩
  · intro row n
    exact labelledCoordinateForm_eval_sparsePair_first row u v A B hU n
  · intro row n
    exact labelledCoordinateForm_eval_sparsePair_second row u v A B hV n

/-- The actual threshold trace of translating every row by one sparse
parameter. -/
noncomputable def sparseQParameterThresholdTrace
    {ρ : Type*} [Fintype ρ]
    (rowU rowV : ρ → RealL2) (threshold : ρ → ℝ) (u v : RealL2) : Finset ρ := by
  classical
  exact Finset.univ.filter fun r ↦
    threshold r ≤ qSeminorm (WithLp.toLp 2 (rowU r + u, rowV r + v))

/-- An unlabelled parameter supported on at most `k` coordinates produces a
trace in the global finite sparse trace collection. -/
theorem sparseQParameterThresholdTrace_mem_sparseParameterThresholdTraces
    {ρ : Type*} [Fintype ρ] {m k : ℕ}
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (threshold : ρ → ℝ)
    (hsupport : ∀ r, (firstSupport r).card + (secondSupport r).card ≤ m)
    (hrowU : ∀ r n, n ∉ firstSupport r → rowU r n = 0)
    (hrowV : ∀ r n, n ∉ secondSupport r → rowV r n = 0)
    (u v : RealL2) (A B : Finset ℕ)
    (hU : ∀ n, n ∉ A → u n = 0)
    (hV : ∀ n, n ∉ B → v n = 0)
    (hcard : A.card + B.card ≤ k) :
    sparseQParameterThresholdTrace rowU rowV threshold u v ∈
      sparseParameterThresholdTraces m k
        rowU rowV firstSupport secondSupport threshold := by
  classical
  let ℓ := sparsePairLabelCount A B
  let copy := sparsePairCopy A B
  let index := sparsePairIndex A B
  let t := sparsePairAmplitude u v A B
  have hℓ : ℓ ≤ k := by
    simpa [ℓ] using hcard
  have hmem := fixedTypeSymbolicThresholdTrace_mem_sparseParameterThresholdTraces
    rowU rowV firstSupport secondSupport threshold copy index t hℓ
    hsupport hrowU hrowV
  have htrace : fixedTypeSymbolicThresholdTrace
      rowU rowV firstSupport secondSupport copy index threshold t =
      sparseQParameterThresholdTrace rowU rowV threshold u v := by
    ext r
    rw [mem_fixedTypeSymbolicThresholdTrace_iff_qSeminorm
      rowU rowV firstSupport secondSupport copy index threshold t r
      (rowU r + u) (rowV r + v) (hrowU r) (hrowV r)]
    · simp [sparseQParameterThresholdTrace]
    · intro n
      simpa [copy, index, t] using
        (labelledCoordinateForm_eval_sparsePair_first
          (fun i ↦ rowU r i) u v A B hU n).symm
    · intro n
      simpa [copy, index, t] using
        (labelledCoordinateForm_eval_sparsePair_second
          (fun i ↦ rowV r i) u v A B hV n).symm
  rw [← htrace]
  exact hmem

/-- A function vanishes outside the finset obtained from its finite function
support. -/
theorem eq_zero_outside_support_toFinset (u : RealL2)
    (hfinite : (Function.support fun n ↦ u n).Finite) :
    ∀ n, n ∉ hfinite.toFinset → u n = 0 := by
  intro n hn
  by_contra hne
  apply hn
  exact hfinite.mem_toFinset.mpr hne

/-- Coverage theorem stated directly using the unlabelled function supports
of the sparse parameter. -/
theorem sparseQParameterThresholdTrace_mem_of_support_ncard_le
    {ρ : Type*} [Fintype ρ] {m k : ℕ}
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (threshold : ρ → ℝ)
    (hsupport : ∀ r, (firstSupport r).card + (secondSupport r).card ≤ m)
    (hrowU : ∀ r n, n ∉ firstSupport r → rowU r n = 0)
    (hrowV : ∀ r n, n ∉ secondSupport r → rowV r n = 0)
    (u v : RealL2)
    (hUfinite : (Function.support fun n ↦ u n).Finite)
    (hVfinite : (Function.support fun n ↦ v n).Finite)
    (hcard : (Function.support fun n ↦ u n).ncard +
      (Function.support fun n ↦ v n).ncard ≤ k) :
    sparseQParameterThresholdTrace rowU rowV threshold u v ∈
      sparseParameterThresholdTraces m k
        rowU rowV firstSupport secondSupport threshold := by
  let A := hUfinite.toFinset
  let B := hVfinite.toFinset
  apply sparseQParameterThresholdTrace_mem_sparseParameterThresholdTraces
    rowU rowV firstSupport secondSupport threshold
    hsupport hrowU hrowV u v A B
  · exact eq_zero_outside_support_toFinset u hUfinite
  · exact eq_zero_outside_support_toFinset v hVfinite
  · dsimp [A, B]
    rw [← Set.ncard_eq_toFinset_card _ hUfinite,
      ← Set.ncard_eq_toFinset_card _ hVfinite]
    exact hcard

/-- Supplementary vector-valued sparse trace theorem: one finite trace collection
of degree `2k` covers every parameter whose two function supports have total
cardinality at most `k`. -/
theorem exists_polynomial_sparse_q_trace_cover
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] (m k : ℕ)
    (rowU rowV : ρ → RealL2) (firstSupport secondSupport : ρ → Finset ℕ)
    (threshold : ρ → ℝ)
    (hsupport : ∀ r, (firstSupport r).card + (secondSupport r).card ≤ m)
    (hrowU : ∀ r n, n ∉ firstSupport r → rowU r n = 0)
    (hrowV : ∀ r n, n ∉ secondSupport r → rowV r n = 0) :
    ∃ traces : Finset (Finset ρ),
      traces.card ≤ sparseTracePolynomialConstant m k *
          (Fintype.card ρ + 1) ^ (2 * k) ∧
        ∀ (u v : RealL2),
          (Function.support fun n ↦ u n).Finite →
          (Function.support fun n ↦ v n).Finite →
          (Function.support fun n ↦ u n).ncard +
              (Function.support fun n ↦ v n).ncard ≤ k →
          sparseQParameterThresholdTrace rowU rowV threshold u v ∈ traces := by
  refine ⟨sparseParameterThresholdTraces m k
    rowU rowV firstSupport secondSupport threshold, ?_, ?_⟩
  · exact card_sparseParameterThresholdTraces_le_polynomial
      m k rowU rowV firstSupport secondSupport threshold hsupport
  · intro u v hUfinite hVfinite hcard
    exact sparseQParameterThresholdTrace_mem_of_support_ncard_le
      rowU rowV firstSupport secondSupport threshold
      hsupport hrowU hrowV u v hUfinite hVfinite hcard

end NormFormula.HalfGraph
