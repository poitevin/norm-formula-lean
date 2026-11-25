import NormFormula.Combinatorics.SparseApproximation
import NormFormula.Combinatorics.ElementarySparseTrace
import NormFormula.Combinatorics.TruncationApproximation

/-!
# Finite fat-shattering for bounded translates of `q`

We apply the general sparse-approximation criterion to coordinate truncation
and the elementary polynomial sparse trace theorem. Fat-shattering `n` rows
forces `2^n` distinct truncated threshold traces, whereas the sparse trace
theorem supplies only polynomially many.
-/

namespace NormFormula.HalfGraph

/-- Parameters in the closed Hilbert ball of radius `R`. -/
abbrev HilbertBallParameter (R : ℝ) := {y : HilbertSpace // ‖y‖ ≤ R}

/-- The family of bounded translates of `q`, evaluated on prescribed rows. -/
noncomputable def qTranslationValue {ρ : Type*} (rows : ρ → HilbertSpace) (R : ℝ) :
    ρ → HilbertBallParameter R → ℝ :=
  fun r y ↦ qSeminorm (rows r + y.1)


/-- The first support of a truncated Hilbert vector is finite. -/
theorem support_truncate_fst_finite (z : HilbertSpace) {η : ℝ} (hη : 0 < η) :
    (Function.support fun n ↦ (truncate z η).fst n).Finite := by
  rw [truncate_fst, support_truncateSequence z.fst hη]
  exact largeCoordinates_finite z.fst hη

/-- The second support of a truncated Hilbert vector is finite. -/
theorem support_truncate_snd_finite (z : HilbertSpace) {η : ℝ} (hη : 0 < η) :
    (Function.support fun n ↦ (truncate z η).snd n).Finite := by
  rw [truncate_snd, support_truncateSequence z.snd hη]
  exact largeCoordinates_finite z.snd hη


/-- The support condition counts coordinates across the two copies of `ℓ₂`.
Both supports must be finite. -/
def HasQSparseSupport (m : ℕ) (z : HilbertSpace) : Prop :=
  (Function.support z.fst).Finite ∧ (Function.support z.snd).Finite ∧
    (Function.support z.fst).ncard + (Function.support z.snd).ncard ≤ m

/-- The elementary count supplies the polynomial hypothesis of the general
sparse-approximation criterion, with no norm bound on sparse parameters. -/
theorem q_hasPolynomialSparseTraces :
    NormFormula.HasPolynomialSparseTraces (fun z ↦ qSeminorm z) HasQSparseSupport := by
  classical
  intro m k
  refine ⟨elementarySparseTraceConstant m k, elementarySparseTraceDegree k, ?_, by positivity, ?_⟩
  · exact_mod_cast elementarySparseTraceConstant_pos m k
  · intro n rows threshold hrows
    let A (r : Fin n) := (hrows r).1.toFinset
    let B (r : Fin n) := (hrows r).2.1.toFinset
    have hsize (r : Fin n) : (A r).card + (B r).card ≤ m := by
      simpa [A, B, ← Set.ncard_eq_toFinset_card] using (hrows r).2.2
    obtain ⟨traces, hcard, hcover⟩ := exists_elementary_sparse_q_trace_cover m k
      (fun r ↦ (rows r).fst) (fun r ↦ (rows r).snd) A B threshold hsize
      (fun r ↦ eq_zero_outside_support_toFinset _ (hrows r).1)
      (fun r ↦ eq_zero_outside_support_toFinset _ (hrows r).2.1)
    refine ⟨traces, ?_, ?_⟩
    · rw [Real.rpow_natCast]
      simp only [Fintype.card_fin] at hcard
      exact_mod_cast hcard
    · intro y hy
      have h := hcover y.fst y.snd hy.1 hy.2.1 hy.2.2
      simpa [NormFormula.thresholdTrace, sparseQParameterThresholdTrace] using h

/-- At every positive scale, there is a uniform finite upper bound on the
size of a row family fat-shattered by bounded translates of `q`. This is an
application of the paper's general criterion with error `4η`. -/
theorem exists_qTranslation_fatShattering_bound
    (R_x R_y ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (n : ℕ) (rows : Fin n → HilbertSpace),
      (∀ r, ‖rows r‖ ≤ R_x) →
      NormFormula.IsFatShattered (qTranslationValue rows R_y) ε → n < N := by
  have hω : Filter.Tendsto (fun η : ℝ ↦ 4 * η)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using ((continuous_const.mul continuous_id).tendsto (0 : ℝ)).mono_left inf_le_left
  obtain ⟨N, hN⟩ := NormFormula.sparse_approximation_criterion
    (fun z ↦ qSeminorm z) HasQSparseSupport (fun η z ↦ truncate z η)
    (fun C η ↦ ⌊C ^ 2 / η ^ 2⌋₊) (fun η ↦ 4 * η)
    (fun η hη C _ z hz ↦ ⟨support_truncate_fst_finite z hη,
      support_truncate_snd_finite z hη, truncate_support_count_le_floor z hz hη⟩)
    (fun η hη x y ↦ abs_qSeminorm_add_sub_truncate_le x y hη)
    hω q_hasPolynomialSparseTraces (max R_x 0) (max R_y 0) ε
    (le_max_right _ _) (le_max_right _ _) hε
  refine ⟨N, fun n rows hrows hfat ↦ hN n rows
    (fun r ↦ (hrows r).trans (le_max_left _ _)) ?_⟩
  exact hfat.reparam
    (fun y : HilbertBallParameter R_y ↦
      (⟨y.1, y.2.trans (le_max_left R_y 0)⟩ : HilbertBallParameter (max R_y 0)))
    (fun _ _ ↦ rfl)

end NormFormula.HalfGraph
