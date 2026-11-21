import NormFormula.Analytic.BanachUltrapower
import NormFormula.Analytic.HilbertStability
import NormFormula.ContinuousLogic.ElementaryDiagramCompactness
import NormFormula.ContinuousLogic.HilbertStableNIP
import NormFormula.ContinuousLogic.FormulaStability

/-! # Hilbert predicates in arbitrary models of a bounded expansion

The elementary diagram realizes each model inside a Hilbert ultrapower.
Thus its named Hilbert translation predicate is again an actual Hilbert norm
translation. The Hilbert norm is stable on bounded sets. Its usual NIP
consequence is applied in that Hilbert model, before combining predicates.
-/
namespace NormFormula.ContinuousLogic
noncomputable section
open Filter NormFormula BanachUltrapower
open scoped Topology
universe u
attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.parameterPseudoMetricSpace MultiStructure.rowNonempty
  MultiStructure.parameterNonempty

/-- Transfer the Hilbert interpretation, including its bounded balls, to
any model with the same complete expanded theory. -/
theorem hilbertPredicate_representation
    {Symbol H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M N : MultiStructure.{u,u,u} Symbol) (hTheory : MultiSameCompleteTheory M N)
    (φ : MultiFormula Symbol 1 1) (r : M.Row → H) (p : M.Parameter → H)
    (R S B : ℝ) (_hB : 0 < B)
    (hr : ∀ x, ‖r x‖ ≤ R) (hp : ∀ y, ‖p y‖ ≤ S)
    (hv : ∀ x y, φ.binaryValue M x y = ‖r x + p y‖ / B) :
    ∃ (r' : N.Row → BanachUltrapower (elementaryDiagramUltrafilter N) H)
      (p' : N.Parameter → BanachUltrapower (elementaryDiagramUltrafilter N) H),
      (∀ x, ‖r' x‖ ≤ R) ∧ (∀ y, ‖p' y‖ ≤ S) ∧
      ∀ x y, φ.binaryValue N x y = ‖r' x + p' y‖ / B := by
  classical
  have hc (i : ElementaryDiagramIndex N) :
      Nonempty (FiniteNamedDiagramRealization id M N i.1 (elementaryDiagramError i)) := by
    apply exists_finiteNamedDiagramRealization id M N
    · intro fragment ε hε
      simpa only [MultiFormula.map_id] using
        fragment.approximately_realized_of_sameCompleteTheory hTheory ε hε
    · exact elementaryDiagramError_pos i
  let c (i : ElementaryDiagramIndex N) := Classical.choice (hc i)
  let U := elementaryDiagramUltrafilter N
  let rf (x : N.Row) := boundedFamily (fun i ↦ r ((c i).rows x)) R (fun i ↦ hr _)
  let pf (y : N.Parameter) := boundedFamily (fun i ↦ p ((c i).parameters y)) S (fun i ↦ hp _)
  refine ⟨fun x ↦ ofBounded U (rf x), fun y ↦ ofBounded U (pf y),
    fun x ↦ norm_ofBounded_le U _ (Eventually.of_forall fun i ↦ hr _),
    fun y ↦ norm_ofBounded_le U _ (Eventually.of_forall fun i ↦ hp _), ?_⟩
  intro x y
  let condition : NamedDiagramCondition N :=
    { rowVars := 1, parameterVars := 1, formula := φ,
      rows := fun _ ↦ x, parameters := fun _ ↦ y }
  have hdist : ∀ᶠ i in U,
      dist (φ.binaryValue M ((c i).rows x) ((c i).parameters y))
        (φ.binaryValue N x y) ≤ elementaryDiagramError i := by
    filter_upwards [eventually_condition_mem_elementaryDiagramUltrafilter condition] with i hi
    simpa [condition, NamedDiagramCondition.target, MultiFormula.binaryValue,
      Real.dist_eq, MultiFormula.map_id] using ((c i).realizes condition hi).le
  have hvalue : Tendsto
      (fun i ↦ φ.binaryValue M ((c i).rows x) ((c i).parameters y)) U
      (𝓝 (φ.binaryValue N x y)) :=
    tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero'
      (Eventually.of_forall fun _ ↦ dist_nonneg) hdist (tendsto_elementaryDiagramError_zero N))
  have hnorm := (tendsto_norm_ofBounded U (rf x + pf y)).div_const B
  rw [ofBounded_add] at hnorm
  exact tendsto_nhds_unique hvalue (by simpa [rf, pf, boundedFamily, hv] using hnorm)

/-- The interpreted Hilbert predicate is stable in every model of the
complete expansion theory, as asserted in Section 4.3. -/
theorem hilbertPredicate_isStableInCompleteTheory
    {Symbol H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : MultiStructure.{u,u,u} Symbol) (φ : MultiFormula Symbol 1 1)
    (r : M.Row → H) (p : M.Parameter → H)
    (R S B : ℝ) (hB : 0 < B)
    (hr : ∀ x, ‖r x‖ ≤ R) (hp : ∀ y, ‖p y‖ ≤ S)
    (hv : ∀ x y, φ.binaryValue M x y = ‖r x + p y‖ / B) :
    MultiFormula.IsStableInCompleteTheory M φ := by
  intro N hTheory
  obtain ⟨r', p', hr', hp', hv'⟩ :=
    hilbertPredicate_representation M N hTheory φ r p R S B hB hr hp hv
  change IsStableKernel (φ.binaryValue N)
  have hfun : φ.binaryValue N = fun x y ↦ ‖r' x + p' y‖ / B :=
    funext fun x ↦ funext (hv' x)
  rw [hfun]
  exact hilbert_norm_isStableOnBounded.normalized_comap
    r' p' R S B hB.ne' hr' hp'

/-- A normalized Hilbert translation predicate is NIP in the complete
expanded theory, through its Hilbert interpretation in each model. -/
theorem hilbertPredicate_isNIPInCompleteTheory
    {Symbol H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : MultiStructure.{u,u,u} Symbol) (φ : MultiFormula Symbol 1 1)
    (r : M.Row → H) (p : M.Parameter → H)
    (R S B : ℝ) (hB : 0 < B)
    (hr : ∀ x, ‖r x‖ ≤ R) (hp : ∀ y, ‖p y‖ ≤ S)
    (hv : ∀ x y, φ.binaryValue M x y = ‖r x + p y‖ / B) :
    MultiFormula.IsNIPInCompleteTheory M φ := by
  rintro ⟨N, hTheory, low, high, hgap, rows, hip⟩
  obtain ⟨r', p', hr', hp', hv'⟩ :=
    hilbertPredicate_representation M N hTheory φ r p R S B hB hr hp hv
  apply Hilbert.not_hasBoundedInfiniteIPWitness
    (H := BanachUltrapower (elementaryDiagramUltrafilter N) H)
    (mul_lt_mul_of_pos_right hgap hB) (R := R) (S := S)
  refine ⟨fun i ↦ r' (rows i), fun i ↦ hr' _, ?_⟩
  intro A C hAC
  obtain ⟨y, hylo, hyhi⟩ := hip A C hAC
  refine ⟨p' y, hp' y, ?_, ?_⟩
  · intro i hi
    have h := hylo i hi
    rw [hv'] at h
    exact (div_le_iff₀ hB).mp h
  · intro i hi
    have h := hyhi i hi
    rw [hv'] at h
    exact (le_div_iff₀ hB).mp h

end
end NormFormula.ContinuousLogic
