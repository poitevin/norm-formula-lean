import NormFormula.ContinuousLogic.HilbertPredicateTransfer
import NormFormula.ContinuousLogic.ContinuousConnectiveNIP
import NormFormula.ContinuousLogic.FormulaIdentity
import NormFormula.ContinuousLogic.NormAddSeparableIP
import NormFormula.ContinuousLogic.BanachBallMixedNormAddReduct

/-! # General Hilbert--seminorm criterion

Name the Hilbert norm and the seminorm on each bounded ball. Transfer the
Hilbert interpretation to every expansion model, use Hilbert stability,
and combine the two NIP predicates by an arbitrary continuous connective.
Finite-box compactness then gives the full standard Banach-ball conclusion.
-/
namespace NormFormula.ContinuousLogic
noncomputable section
universe u

inductive HilbertSparseSymbol : Type u
  | norm | hilbert | seminorm
  deriving DecidableEq

variable {E H : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A dominated seminorm is uniformly continuous for the ambient norm. -/
theorem seminorm_uniformContinuous_of_le_norm (p : Seminorm ℝ E)
    (hp : ∀ x, p x ≤ ‖x‖) : UniformContinuous p := by
  apply (show LipschitzWith 1 p from ?_).uniformContinuous
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [dist_eq_norm] using (p.norm_sub_map_le_sub x y).trans (hp (x-y))

/-- A seminorm normalized on a common positive ball. -/
def seminormAddTruth (p : Seminorm ℝ E) (hp : ∀ x, p x ≤ ‖x‖)
    (R : ℝ) (hR : 0 < R) (x y : PositiveNormBall E R) : TruthValue :=
  ⟨p (x.1 + y.1) / (2*R), div_nonneg (apply_nonneg p _) (by positivity),
    (div_le_one (by positivity)).mpr ((hp _).trans
      ((norm_add_le _ _).trans (by linarith [x.2,y.2])))⟩

theorem seminormAddTruth_uniformContinuous (p : Seminorm ℝ E)
    (hp : ∀ x, p x ≤ ‖x‖) (R : ℝ) (hR : 0 < R) :
    UniformContinuous fun z : PositiveNormBall E R × PositiveNormBall E R ↦
      seminormAddTruth p hp R hR z.1 z.2 :=
  (((seminorm_uniformContinuous_of_le_norm p hp).comp
    ((uniformContinuous_subtype_val.comp uniformContinuous_fst).add
      (uniformContinuous_subtype_val.comp uniformContinuous_snd))).div_const' (2*R)).subtype_mk _

def hilbertSparseStructure (e : E →ₗ[ℝ] H) (he : ∀ x, ‖e x‖ ≤ ‖x‖)
    (p : Seminorm ℝ E) (hp : ∀ x, p x ≤ ‖x‖) (R : ℝ) (hR : 0 < R) :
    MultiStructure.{u,u,u} HilbertSparseSymbol.{u} where
  Row := PositiveNormBall E R
  Parameter := PositiveNormBall E R
  rowNonempty := ⟨⟨0, by simpa using hR.le⟩⟩
  parameterNonempty := ⟨⟨0, by simpa using hR.le⟩⟩
  predicate
    | .norm => normAddTruth R hR
    | .hilbert => seminormAddTruth ((normSeminorm ℝ H).comp e) he R hR
    | .seminorm => seminormAddTruth p hp R hR
  predicate_uniformContinuous := by
    intro s
    cases s
    · exact normAddTruth_uniformContinuous R hR
    · exact seminormAddTruth_uniformContinuous _ _ _ _
    · exact seminormAddTruth_uniformContinuous _ _ _ _

omit [NormedSpace ℝ E] in
/-- Finite-pattern bounds for a real predicate imply NIP of its named
normalization in any bounded expansion. -/
theorem normalizedPredicate_isNIPInCompleteTheory
    {Symbol : Type u} (M : MultiStructure.{u,u,u} Symbol)
    (φ : MultiFormula Symbol 1 1) (value : E → E → ℝ)
    (r : M.Row → E) (p : M.Parameter → E) (R S B : ℝ) (hB : 0 < B)
    (hr : ∀ x, ‖r x‖ ≤ R) (hp : ∀ y, ‖p y‖ ≤ S)
    (hv : ∀ x y, φ.binaryValue M x y = value (r x) (p y) / B)
    (hlocal : IsBoundedLocalNIP value) : MultiFormula.IsNIPInCompleteTheory M φ := by
  apply MultiFormula.isNIPInCompleteTheory_of_no_finiteIPPatterns
  intro low high hgap hall
  apply hlocal.not_hasIPPatternsInEveryDimension (mul_lt_mul_of_pos_right hgap hB)
    (R_x := R) (R_y := S)
  intro n
  obtain ⟨rows, hrows⟩ := hall n
  refine ⟨fun i ↦ r (rows i), fun i ↦ hr _, ?_⟩
  intro A
  obtain ⟨y, hhi, hlo⟩ := hrows A
  refine ⟨⟨p y, hp y⟩, ?_, ?_⟩
  · intro i hi
    have h := hhi i hi
    dsimp only at h
    rw [hv] at h
    exact (le_div_iff₀ hB).mp h
  · intro i hi
    have h := hlo i hi
    dsimp only at h
    rw [hv] at h
    exact (div_le_iff₀ hB).mp h

/-- The general complete-expansion theorem. No Hilbert dimension or
separability restriction is imposed. -/
theorem hilbert_sparse_norm_isNIPInExpansion
    (e : E →ₗ[ℝ] H) (he : ∀ x, ‖e x‖ ≤ ‖x‖)
    (p : Seminorm ℝ E) (hp : ∀ x, p x ≤ ‖x‖)
    (hlocal : IsBoundedLocalNIP (fun x y ↦ p (x+y)))
    (R : ℝ) (hR : 0 < R) (gate : Connective 2)
    (hrec : ∀ x y : PositiveNormBall E R,
      normAddTruth R hR x y = gate ![
        seminormAddTruth ((normSeminorm ℝ H).comp e) he R hR x y,
        seminormAddTruth p hp R hR x y]) :
    MultiFormula.IsNIPInCompleteTheory (hilbertSparseStructure e he p hp R hR)
      (.predicate .norm 0 0) := by
  let M := hilbertSparseStructure e he p hp R hR
  let fs : Fin 2 → MultiFormula HilbertSparseSymbol.{u} 1 1 :=
    ![.predicate .hilbert 0 0, .predicate .seminorm 0 0]
  apply MultiFormula.nip_of_equivalent
    (MultiFormula.equivalentInCompleteTheory_of_binaryValue_eq
      (.predicate .norm 0 0) (.connective gate fs) (by
        intro x y
        apply congrArg Subtype.val
        change normAddTruth R hR x y = _
        rw [hrec]
        congr 1
        funext i
        fin_cases i <;> rfl))
  apply MultiFormula.isNIPInCompleteTheory_connective
  intro j
  fin_cases j
  · apply hilbertPredicate_isNIPInCompleteTheory M (.predicate .hilbert 0 0)
      (fun x ↦ e x.1) (fun y ↦ e y.1) R R (2*R) (by positivity)
      (fun x ↦ (he x.1).trans x.2) (fun y ↦ (he y.1).trans y.2)
    intro x y
    change ‖e (x.1+y.1)‖ / (2*R) = _
    rw [map_add]
  · exact normalizedPredicate_isNIPInCompleteTheory M (.predicate .seminorm 0 0)
      (fun x y ↦ p (x+y)) Subtype.val Subtype.val R R (2*R) (by positivity)
      (fun x ↦ x.2) (fun y ↦ y.2) (fun _ _ ↦ rfl) hlocal

/-- The expansion conclusion gives uniform finite norm-pattern bounds.
This is the finite-box reduct-transfer argument. -/
theorem hilbert_sparse_norm_isBoundedLocalNIP
    (e : E →ₗ[ℝ] H) (he : ∀ x, ‖e x‖ ≤ ‖x‖)
    (p : Seminorm ℝ E) (hp : ∀ x, p x ≤ ‖x‖)
    (hlocal : IsBoundedLocalNIP (fun x y ↦ p (x+y)))
    (gate : Connective 2)
    (hrec : ∀ (R : ℝ) (hR : 0 < R) (x y : PositiveNormBall E R),
      normAddTruth R hR x y = gate ![
        seminormAddTruth ((normSeminorm ℝ H).comp e) he R hR x y,
        seminormAddTruth p hp R hR x y]) :
    IsBoundedLocalNIP (fun x y : E ↦ ‖x+y‖) := by
  apply isBoundedLocalNIP_of_no_patterns
  intro R S low high hgap hall
  let B := 1 + |R| + |S|
  have hB : 0 < B := by dsimp [B]; positivity
  let M := hilbertSparseStructure e he p hp B hB
  let bounds : M.Bounds :=
    ⟨(normAddMultiStructureBounds B hB).row, (normAddMultiStructureBounds B hB).parameter⟩
  apply hilbert_sparse_norm_isNIPInExpansion e he p hp hlocal B hB gate (hrec B hB)
  apply MultiFormula.atomic_hasIPInCompleteTheory_of_finitePatterns M bounds .norm
    (low / (2*B)) (high / (2*B))
    ((div_lt_div_iff_of_pos_right (by positivity)).mpr hgap)
  exact normAddMulti_hasFinitePatterns_of_raw_patterns R S low high hall

/-- Complete standard Banach-ball-theory NIP, at all independent rational
row and parameter radii, follows from the Hilbert--seminorm criterion. -/
theorem hilbert_sparse_norm_fullTheoryNIP [CompleteSpace E]
    (e : E →ₗ[ℝ] H) (he : ∀ x, ‖e x‖ ≤ ‖x‖)
    (p : Seminorm ℝ E) (hp : ∀ x, p x ≤ ‖x‖)
    (hlocal : IsBoundedLocalNIP (fun x y ↦ p (x+y)))
    (gate : Connective 2)
    (hrec : ∀ (R : ℝ) (hR : 0 < R) (x y : PositiveNormBall E R),
      normAddTruth R hR x y = gate ![
        seminormAddTruth ((normSeminorm ℝ H).comp e) he R hR x y,
        seminormAddTruth p hp R hR x y])
    (rowRadius parameterRadius : ℚ≥0) :
    (predicateFreeNormAddFormula rowRadius parameterRadius).IsNIPInCompleteTheory
      (standardBanachBallStructure E) := by
  apply BallFormula.isNIPInCompleteTheory_of_mixedNormAddMulti
  apply normAddMultiFormula_isNIPInCompleteTheory_ballNormAddMixedMultiStructure_of_boundedLocalNIP
  exact hilbert_sparse_norm_isBoundedLocalNIP e he p hp hlocal gate hrec

end
end NormFormula.ContinuousLogic
