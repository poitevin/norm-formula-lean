import NormFormula.Combinatorics.ElementaryQForms
import NormFormula.Combinatorics.SparseParameterRepresentation

/-!
# The elementary sparse trace bound of Section 4.2

Order types contribute degree `k`; the real partitions for the single and
pair sums contribute degree `k + choose k 2`. Only distinct coordinate labels
are needed to represent actual sparse parameters. The proof below uses the
finite-support and order-transport lemmas, not the hyperplane counting bound.
-/

namespace NormFormula.HalfGraph

theorem distinctCoordinateLabels_of_same_type {ℓ : ℕ} {D : Finset ℕ}
    {copy copy' : Fin ℓ → CoordinateCopy} {index index' : Fin ℓ → ℕ}
    (h : sparseOrderType D copy index = sparseOrderType D copy' index')
    (hdist : DistinctCoordinateLabels copy index) : DistinctCoordinateLabels copy' index' := by
  intro a b hab
  apply hdist
  apply Prod.ext
  · exact (sparseOrderType_eq_preserves_copy h a).trans
      ((congrArg Prod.fst hab).trans (sparseOrderType_eq_preserves_copy h b).symm)
  · exact (natOrderRelation_eq_preserves_eq
      (sparseOrderType_eq_preserves_pair_relation h a b)).mpr (congrArg Prod.snd hab)

theorem card_fixedTypeTraces_le_elementary
    {ρ : Type*} [Fintype ρ] {ℓ m : ℕ}
    (rowU rowV : ρ → RealL2) (A B : ρ → Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ) (threshold : ρ → ℝ)
    (hdist : DistinctCoordinateLabels copy index)
    (hsize : ∀ r, (A r).card + (B r).card ≤ m)
    (hU : ∀ r n, n ∉ A r → rowU r n = 0)
    (hV : ∀ r n, n ∉ B r → rowV r n = 0) :
    (realizableFixedTypeSymbolicThresholdTraces rowU rowV A B copy index threshold).card ≤
      (4 * Fintype.card ρ * (m + 1) ^ 2 + 1) ^ elementaryExpressionCount ℓ := by
  apply card_realizableRowThresholdTraces_le_elementary
    (symbolicRowQForms rowU rowV A B copy index)
    (fun r ↦ rowConstantSums (fun n ↦ rowU r n) (fun n ↦ rowV r n) (A r) (B r)) threshold
  · intro r
    exact card_rowConstantSums_le _ _ _ _ m (hsize r)
  · intro r f hf
    exact symbolicAffineQForm_elementary _ _ _ _ copy index hdist (hU r) (hV r) f hf

noncomputable def elementaryTracesForCode
    {ρ : Type*} [Fintype ρ] {ℓ : ℕ}
    (rowU rowV : ρ → RealL2) (A B : ρ → Finset ℕ)
    (threshold : ρ → ℝ) (D : Finset ℕ) (τ : SparseOrderType D ℓ) : Finset (Finset ρ) := by
  classical
  let p := sparseCodeRepresentative D τ
  exact if DistinctCoordinateLabels p.copy p.index then
    realizableFixedTypeSymbolicThresholdTraces rowU rowV A B p.copy p.index threshold else ∅

noncomputable def elementaryFixedLabelTraces
    {ρ : Type*} [Fintype ρ] (ℓ : ℕ)
    (rowU rowV : ρ → RealL2) (A B : ρ → Finset ℕ)
    (threshold : ρ → ℝ) (D : Finset ℕ) : Finset (Finset ρ) := by
  classical
  exact Finset.univ.biUnion (elementaryTracesForCode (ℓ := ℓ) rowU rowV A B threshold D)

noncomputable def elementarySparseParameterTraces
    {ρ : Type*} [Fintype ρ] (m k : ℕ)
    (rowU rowV : ρ → RealL2) (A B : ρ → Finset ℕ)
    (threshold : ρ → ℝ) : Finset (Finset ρ) := by
  classical
  exact (Finset.range (k + 1)).biUnion fun ℓ ↦
    elementaryFixedLabelTraces ℓ rowU rowV A B threshold (sparseTraceProtectedSet A B m k)

theorem fixedTypeTrace_mem_elementarySparseParameterTraces
    {ρ : Type*} [Fintype ρ] {ℓ m k : ℕ}
    (rowU rowV : ρ → RealL2) (A B : ρ → Finset ℕ) (threshold : ρ → ℝ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ) (t : Fin ℓ → ℝ)
    (hℓ : ℓ ≤ k) (hdist : DistinctCoordinateLabels copy index)
    (hsize : ∀ r, (A r).card + (B r).card ≤ m)
    (hU : ∀ r n, n ∉ A r → rowU r n = 0)
    (hV : ∀ r n, n ∉ B r → rowV r n = 0) :
    fixedTypeSymbolicThresholdTrace rowU rowV A B copy index threshold t ∈
      elementarySparseParameterTraces m k rowU rowV A B threshold := by
  classical
  let D := sparseTraceProtectedSet A B m k
  let p : LabelledSparseRealization ℓ := ⟨copy, index⟩
  let τ := p.code D
  let rep := sparseCodeRepresentative D τ
  have hrep := sparseCodeRepresentative_code_eq D τ ⟨p, rfl⟩
  have htype : sparseOrderType D copy index = sparseOrderType D rep.copy rep.index := hrep.symm
  have hdist' := distinctCoordinateLabels_of_same_type htype hdist
  have hforms := symbolicRowQForms_eq_of_sparseOrderType_eq (s := m + k)
    rowU rowV A B htype
    (firstSupport_subset_sparseTraceProtectedSet A B m k)
    (secondSupport_subset_sparseTraceProtectedSet A B m k) hU hV
    (fun r ↦ by have := hsize r; omega)
    (initialBlock_subset_sparseTraceProtectedSet A B m k)
  have htrace : fixedTypeSymbolicThresholdTrace rowU rowV A B copy index threshold t =
      fixedTypeSymbolicThresholdTrace rowU rowV A B rep.copy rep.index threshold t := by
    unfold fixedTypeSymbolicThresholdTrace
    rw [hforms]
  unfold elementarySparseParameterTraces elementaryFixedLabelTraces
  apply Finset.mem_biUnion.mpr
  refine ⟨ℓ, Finset.mem_range.mpr (by omega), Finset.mem_biUnion.mpr ⟨τ, Finset.mem_univ τ, ?_⟩⟩
  change _ ∈ elementaryTracesForCode rowU rowV A B threshold D τ
  unfold elementaryTracesForCode
  dsimp only
  rw [if_pos hdist']
  exact (mem_realizableFixedTypeSymbolicThresholdTraces _ _ _ _ _ _ _ _).mpr ⟨t, htrace.symm⟩

def elementarySparseTraceDegree (k : ℕ) : ℕ := k + elementaryExpressionCount k

theorem elementarySparseTraceDegree_eq (k : ℕ) :
    elementarySparseTraceDegree k = 2 * k + k.choose 2 := by
  unfold elementarySparseTraceDegree elementaryExpressionCount
  omega

def elementarySparseTraceConstant (m k : ℕ) : ℕ :=
  (k + 1) * (orderTypeConstant k * (2 * (m + (m + k + 1)) + 1) ^ k *
    (4 * (m + 1) ^ 2 + 1) ^ elementaryExpressionCount k)

theorem elementarySparseTraceConstant_pos (m k : ℕ) : 0 < elementarySparseTraceConstant m k := by
  unfold elementarySparseTraceConstant orderTypeConstant
  positivity

theorem elementaryExpressionCount_mono {ℓ k : ℕ} (h : ℓ ≤ k) :
    elementaryExpressionCount ℓ ≤ elementaryExpressionCount k :=
  Nat.add_le_add h (Nat.choose_le_choose 2 h)

theorem card_elementarySparseParameterTraces_le
    {ρ : Type*} [Fintype ρ] (m k : ℕ)
    (rowU rowV : ρ → RealL2) (A B : ρ → Finset ℕ) (threshold : ρ → ℝ)
    (hsize : ∀ r, (A r).card + (B r).card ≤ m)
    (hU : ∀ r n, n ∉ A r → rowU r n = 0)
    (hV : ∀ r n, n ∉ B r → rowV r n = 0) :
    (elementarySparseParameterTraces m k rowU rowV A B threshold).card ≤
      elementarySparseTraceConstant m k * (Fintype.card ρ + 1) ^ elementarySparseTraceDegree k := by
  classical
  let n := Fintype.card ρ
  let D := sparseTraceProtectedSet A B m k
  let U := 2 * (m + (m + k + 1)) + 1
  let V := 4 * (m + 1) ^ 2 + 1
  let K := orderTypeConstant k * U ^ k * V ^ elementaryExpressionCount k
  have hD := card_sparseTraceProtectedSet_le A B m k hsize
  have hcode (ℓ : ℕ) (hℓ : ℓ ≤ k) :
      Fintype.card (SparseOrderType D ℓ) ≤ orderTypeConstant k * (U * (n + 1)) ^ k := by
    rw [card_sparseOrderType]
    apply Nat.mul_le_mul (orderTypeConstant_mono hℓ)
    apply (pow_le_pow_left' (show 2 * D.card + 1 ≤ U * (n + 1) from
      (by have hb := protectedOrderBase_le n m k; dsimp [D, U, n] at *; omega)) ℓ).trans
    exact pow_le_pow_right' (by change 0 < U * (n + 1); dsimp [U]; positivity) hℓ
  have hbase : 4 * n * (m + 1) ^ 2 + 1 ≤ V * (n + 1) := by dsimp [V]; nlinarith
  have hfixed (ℓ : ℕ) (hℓ : ℓ ≤ k) :
      (elementaryFixedLabelTraces ℓ rowU rowV A B threshold D).card ≤
        K * (n + 1) ^ elementarySparseTraceDegree k := by
    have htype (τ : SparseOrderType D ℓ) :
        (elementaryTracesForCode rowU rowV A B threshold D τ).card ≤
          (V * (n + 1)) ^ elementaryExpressionCount k := by
      unfold elementaryTracesForCode
      dsimp only
      split_ifs with hd
      · exact (card_fixedTypeTraces_le_elementary rowU rowV A B _ _ threshold hd hsize hU hV).trans
          ((pow_le_pow_left' hbase _).trans
            (pow_le_pow_right' (by change 0 < V * (n + 1); dsimp [V]; positivity) (elementaryExpressionCount_mono hℓ)))
      · simp
    have hcount := Finset.card_biUnion_le_card_mul Finset.univ
      (elementaryTracesForCode rowU rowV A B threshold D)
      ((V * (n + 1)) ^ elementaryExpressionCount k) (fun τ _ ↦ htype τ)
    calc
      _ ≤ Fintype.card (SparseOrderType D ℓ) * ((V * (n + 1)) ^ elementaryExpressionCount k) := by
        simpa [elementaryFixedLabelTraces] using hcount
      _ ≤ (orderTypeConstant k * (U * (n + 1)) ^ k) *
          ((V * (n + 1)) ^ elementaryExpressionCount k) := Nat.mul_le_mul_right _ (hcode ℓ hℓ)
      _ = K * (n + 1) ^ elementarySparseTraceDegree k := by
        simp only [K, elementarySparseTraceDegree, mul_pow, pow_add]
        ring
  have hcount := Finset.card_biUnion_le_card_mul (Finset.range (k + 1))
    (fun ℓ ↦ elementaryFixedLabelTraces ℓ rowU rowV A B threshold D)
    (K * (n + 1) ^ elementarySparseTraceDegree k)
    (fun ℓ hℓ ↦ hfixed ℓ (by have := Finset.mem_range.mp hℓ; omega))
  simpa [elementarySparseParameterTraces, elementarySparseTraceConstant, D, K, U, V, n,
    Nat.mul_assoc] using hcount

theorem sparsePair_distinctCoordinateLabels (A B : Finset ℕ) :
    DistinctCoordinateLabels (sparsePairCopy A B) (sparsePairIndex A B) := by
  intro a b hab
  apply (sparsePairLabelEquiv A B).symm.injective
  cases ha : (sparsePairLabelEquiv A B).symm a with
  | inl i =>
    cases hb : (sparsePairLabelEquiv A B).symm b with
    | inl j =>
      have hij : i.1 = j.1 := by simpa [sparsePairIndex, ha, hb] using congrArg Prod.snd hab
      exact congrArg Sum.inl (Subtype.ext hij)
    | inr j => simp [sparsePairCopy, ha, hb] at hab
  | inr i =>
    cases hb : (sparsePairLabelEquiv A B).symm b with
    | inl j => simp [sparsePairCopy, ha, hb] at hab
    | inr j =>
      have hij : i.1 = j.1 := by simpa [sparsePairIndex, ha, hb] using congrArg Prod.snd hab
      exact congrArg Sum.inr (Subtype.ext hij)

/-- The paper's elementary polynomial cover, for arbitrary finite row sets
including the empty set, and arbitrary sparse parameters and thresholds. -/
theorem exists_elementary_sparse_q_trace_cover
    {ρ : Type*} [Fintype ρ] (m k : ℕ)
    (rowU rowV : ρ → RealL2) (A B : ρ → Finset ℕ) (threshold : ρ → ℝ)
    (hsize : ∀ r, (A r).card + (B r).card ≤ m)
    (hU : ∀ r n, n ∉ A r → rowU r n = 0)
    (hV : ∀ r n, n ∉ B r → rowV r n = 0) :
    ∃ traces : Finset (Finset ρ),
      traces.card ≤ elementarySparseTraceConstant m k *
        (Fintype.card ρ + 1) ^ elementarySparseTraceDegree k ∧
      ∀ (u v : RealL2), (Function.support fun n ↦ u n).Finite →
        (Function.support fun n ↦ v n).Finite →
        (Function.support fun n ↦ u n).ncard + (Function.support fun n ↦ v n).ncard ≤ k →
        sparseQParameterThresholdTrace rowU rowV threshold u v ∈ traces := by
  classical
  refine ⟨elementarySparseParameterTraces m k rowU rowV A B threshold,
    card_elementarySparseParameterTraces_le m k rowU rowV A B threshold hsize hU hV, ?_⟩
  intro u v hu hv hcard
  let U := hu.toFinset
  let V := hv.toFinset
  let copy := sparsePairCopy U V
  let index := sparsePairIndex U V
  let t := sparsePairAmplitude u v U V
  have hℓ : sparsePairLabelCount U V ≤ k := by
    simpa [U, V, ← Set.ncard_eq_toFinset_card] using hcard
  have hmem := fixedTypeTrace_mem_elementarySparseParameterTraces
    rowU rowV A B threshold copy index t hℓ (sparsePair_distinctCoordinateLabels U V) hsize hU hV
  have htrace : fixedTypeSymbolicThresholdTrace rowU rowV A B copy index threshold t =
      sparseQParameterThresholdTrace rowU rowV threshold u v := by
    ext r
    rw [mem_fixedTypeSymbolicThresholdTrace_iff_qSeminorm
      rowU rowV A B copy index threshold t r (rowU r + u) (rowV r + v) (hU r) (hV r)]
    · simp [sparseQParameterThresholdTrace]
    · intro n
      exact (labelledCoordinateForm_eval_sparsePair_first _ u v U V
        (eq_zero_outside_support_toFinset u hu) n).symm
    · intro n
      exact (labelledCoordinateForm_eval_sparsePair_second _ u v U V
        (eq_zero_outside_support_toFinset v hv) n).symm
  rwa [htrace] at hmem

end NormFormula.HalfGraph
