import NormFormula.Analytic.SeminormRenorm
import NormFormula.Analytic.Separability
import NormFormula.ContinuousLogic.HilbertSparseNIP
import NormFormula.ModelTheory.YLocalNIP
import NormFormula.Examples.HalfGraph
import NormFormula.ModelTheory.BoundedStability

/-! # Bollobás's additive norm `h + εq` -/
namespace NormFormula.Bollobas
noncomputable section
open HalfGraph ContinuousLogic Filter
open scoped Topology NNReal

variable (ε : ℝ) (hε : 0 < ε)

def weightedQ : Seminorm ℝ HilbertSpace :=
  Seminorm.of (fun x ↦ ε*qSeminorm x)
    (fun x y ↦ by nlinarith [mul_le_mul_of_nonneg_left (map_add_le_add qSeminorm x y) hε.le])
    (fun r x ↦ by dsimp only; rw [map_smul_eq_mul]; ring)

def additiveSeminorm : Seminorm ℝ HilbertSpace := normSeminorm ℝ HilbertSpace + weightedQ ε hε

@[simp] theorem additiveSeminorm_apply (x : HilbertSpace) :
    additiveSeminorm ε hε x = ‖x‖ + ε*qSeminorm x := rfl

theorem lower (x : HilbertSpace) : ‖x‖ ≤ additiveSeminorm ε hε x := by
  rw [additiveSeminorm_apply]
  exact le_add_of_nonneg_right (mul_nonneg hε.le (apply_nonneg _ _))

theorem upper (x : HilbertSpace) :
    additiveSeminorm ε hε x ≤ (1+ε*Real.sqrt 2)*‖x‖ := by
  rw [additiveSeminorm_apply]
  have h := mul_le_mul_of_nonneg_left (qSeminorm_le_sqrtTwo_mul_norm x) hε.le
  nlinarith

abbrev Space := SeminormRenorm (additiveSeminorm ε hε) (lower ε hε)

def hilbertEquiv : Space ε hε ≃L[ℝ] HilbertSpace :=
  SeminormRenorm.continuousLinearEquiv _ _ (1+ε*Real.sqrt 2) (upper ε hε)
instance : CompleteSpace (Space ε hε) :=
  SeminormRenorm.completeSpace _ _ (1+ε*Real.sqrt 2) (upper ε hε)
instance : TopologicalSpace.SeparableSpace (Space ε hε) :=
  SeminormRenorm.separableSpace _ _ (1+ε*Real.sqrt 2) (upper ε hε)

include hε in
/-- Strictly positive scalar multiplication preserves finite-pattern NIP. -/
theorem boundedLocalNIP_const_mul
    {X Y : Type*} [Norm X] [Norm Y] {v : X → Y → ℝ}
    (hv : IsBoundedLocalNIP v) : IsBoundedLocalNIP (fun x y ↦ ε*v x y) := by
  intro R S low high hgap
  obtain ⟨N,hN⟩ := hv R S (low/ε) (high/ε) ((div_lt_div_iff_of_pos_right hε).mpr hgap)
  refine ⟨N, ?_⟩
  intro n rows hrows hp
  apply hN n rows hrows
  intro A
  obtain ⟨y,hhi,hlo⟩ := hp A
  refine ⟨y, ?_, ?_⟩
  · intro i hi
    exact (div_le_iff₀ hε).mpr (by simpa [boundedBinaryValue, mul_comm] using hhi i hi)
  · intro i hi
    exact (le_div_iff₀ hε).mpr (by simpa [boundedBinaryValue, mul_comm] using hlo i hi)

def additionConnective : Connective 2 where
  toFun v := ⟨min 1 ((v 0:ℝ)+(v 1:ℝ)),
    le_min zero_le_one (add_nonneg (v 0).2.1 (v 1).2.1), min_le_left _ _⟩
  continuous_toFun := (continuous_const.min
    ((continuous_subtype_val.comp (continuous_apply 0)).add
      (continuous_subtype_val.comp (continuous_apply 1)))).subtype_mk _

theorem fullTheoryNIP (rowRadius parameterRadius : ℚ≥0) :
    (predicateFreeNormAddFormula rowRadius parameterRadius).IsNIPInCompleteTheory
      (standardBanachBallStructure (Space ε hε)) := by
  let e := (SeminormRenorm.linearEquiv (additiveSeminorm ε hε) (lower ε hε)).toLinearMap
  let p := (weightedQ ε hε).comp e
  have he : ∀ x : Space ε hε, ‖e x‖ ≤ ‖x‖ := fun x ↦ lower ε hε x.val
  have hp : ∀ x : Space ε hε, p x ≤ ‖x‖ := fun x ↦
    le_add_of_nonneg_left (norm_nonneg x.val)
  have hq : IsBoundedLocalNIP (fun x y : Space ε hε ↦ p (x+y)) := by
    have h := (boundedLocalNIP_const_mul ε hε qSeminormTranslate_isBoundedLocalNIP).comap e e he he
    simpa [p, e, weightedQ, qSeminormTranslate, ← map_add] using h
  apply hilbert_sparse_norm_fullTheoryNIP e he p hp hq additionConnective ?_ rowRadius parameterRadius
  intro R hR x y
  apply Subtype.ext
  change ‖x.1+y.1‖/(2*R) = min 1 (‖e (x.1+y.1)‖/(2*R)+p (x.1+y.1)/(2*R))
  rw [← add_div]
  have hid : ‖e (x.1+y.1)‖+p (x.1+y.1) = ‖x.1+y.1‖ := rfl
  rw [hid]
  exact (min_eq_right (normAddTruth R hR x y).2.2).symm

def row (i : ℕ) : Space ε hε := ⟨xVector i⟩
def parameter (j : ℕ) : Space ε hε := ⟨yVector j⟩

theorem half_graph (i j : ℕ) : ‖row ε hε i + parameter ε hε j‖ =
    if i<j then Real.sqrt 2+2*ε else Real.sqrt 2+ε := by
  change ‖xVector i+yVector j‖ + ε*qSeminorm (xVector i+yVector j) = _
  have hn : ‖xVector i+yVector j‖ = Real.sqrt 2 := by
    rw [← norm_sq_x_add_y i j, Real.sqrt_sq (norm_nonneg _)]
  rw [hn]
  by_cases hij : i<j
  · rw [if_pos hij, qSeminorm_x_add_y_of_lt hij]; ring
  · rw [if_neg hij, qSeminorm_x_add_y_of_ge (Nat.le_of_not_gt hij)]; ring

theorem norm_unstable : ¬ IsStableOnBounded (fun x y : Space ε hε ↦ ‖x+y‖) := by
  intro hstable
  have hrow (i : ℕ) : ‖row ε hε i‖ ≤ 1+ε*Real.sqrt 2 := by
    simpa [row,xVector] using upper ε hε (xVector i)
  have hparam (j : ℕ) : ‖parameter ε hε j‖ ≤ 1+ε*Real.sqrt 2 := by
    simpa [parameter,yVector] using upper ε hε (yVector j)
  have hfirst : HasSuccessiveLimit
      (fun i j ↦ ‖row ε hε i+parameter ε hε j‖) (Real.sqrt 2+2*ε) := by
    refine ⟨fun _ ↦ Real.sqrt 2+2*ε, ?_, tendsto_const_nhds⟩
    intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop i] with j hj
    simp [half_graph, hj]
  have hsecond : HasSuccessiveLimit
      (fun j i ↦ ‖row ε hε i+parameter ε hε j‖) (Real.sqrt 2+ε) := by
    refine ⟨fun _ ↦ Real.sqrt 2+ε, ?_, tendsto_const_nhds⟩
    intro j
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop j] with i hi
    simp [half_graph, Nat.not_lt.mpr hi]
  have h := hstable (row ε hε) (parameter ε hε) _ _ _ _ hrow hparam hfirst hsecond
  linarith
end
end NormFormula.Bollobas
