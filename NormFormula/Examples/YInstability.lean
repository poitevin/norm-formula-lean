import Mathlib.Topology.Sequences
import NormFormula.Examples.HalfGraph
import NormFormula.ModelTheory.BoundedStability
import NormFormula.ModelTheory.YNormLocalNIP

/-!
# Instability of the norm on `Y`

The exact half-graph computed earlier has successive limits `√6` and `√3`.
This file records boundedness of its two sequences and turns that computation
into the paper's explicit local-instability conclusion.
-/

namespace NormFormula.HalfGraph.Y

noncomputable section

open Filter
open scoped Topology

/-- The half-graph row sequence is uniformly bounded in `Y`. -/
theorem halfGraphRow_bounded (i : ℕ) :
    ‖HalfGraph.xInY i‖ ≤ Real.sqrt 3 := by
  calc
    ‖HalfGraph.xInY i‖ ≤
        Real.sqrt 3 * ‖(HalfGraph.xInY i).toHilbert‖ :=
      norm_le_sqrtThree_mul_hilbert_norm _
    _ = Real.sqrt 3 := by simp [xInY, HalfGraph.xVector]

/-- The half-graph parameter sequence is uniformly bounded in `Y`. -/
theorem halfGraphParameter_bounded (j : ℕ) :
    ‖HalfGraph.yInY j‖ ≤ Real.sqrt 3 := by
  calc
    ‖HalfGraph.yInY j‖ ≤
        Real.sqrt 3 * ‖(HalfGraph.yInY j).toHilbert‖ :=
      norm_le_sqrtThree_mul_hilbert_norm _
    _ = Real.sqrt 3 := by simp [yInY, HalfGraph.yVector]

/-- Taking the parameter limit first gives the value `√6`. -/
theorem halfGraph_successiveLimit_sqrtSix :
    HasSuccessiveLimit
      (fun i j ↦ normPredicateTranslate
        (HalfGraph.xInY i) (HalfGraph.yInY j))
      (Real.sqrt 6) := by
  refine ⟨fun _ ↦ Real.sqrt 6, ?_, tendsto_const_nhds⟩
  intro i
  rw [show (fun j ↦ normPredicateTranslate
      (HalfGraph.xInY i) (HalfGraph.yInY j)) =
      fun j ↦ if i < j then Real.sqrt 6 else Real.sqrt 3 by
        funext j
        exact HalfGraph.norm_xInY_add_yInY i j]
  refine (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [eventually_gt_atTop i] with j hij
  simp [hij]

/-- Reversing the order gives the value `√3`. -/
theorem halfGraph_reverse_successiveLimit_sqrtThree :
    HasSuccessiveLimit
      (fun j i ↦ normPredicateTranslate
        (HalfGraph.xInY i) (HalfGraph.yInY j))
      (Real.sqrt 3) := by
  refine ⟨fun _ ↦ Real.sqrt 3, ?_, tendsto_const_nhds⟩
  intro j
  rw [show (fun i ↦ normPredicateTranslate
      (HalfGraph.xInY i) (HalfGraph.yInY j)) =
      fun i ↦ if i < j then Real.sqrt 6 else Real.sqrt 3 by
        funext i
        exact HalfGraph.norm_xInY_add_yInY i j]
  refine (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [eventually_ge_atTop j] with i hji
  simp [Nat.not_lt.mpr hji]

/-- The norm formula is unstable on the distinguished space `Y`. -/
theorem normPredicateTranslate_not_isStableOnBounded :
    ¬ IsStableOnBounded normPredicateTranslate := by
  intro hstable
  have heq := hstable HalfGraph.xInY HalfGraph.yInY
    (Real.sqrt 3) (Real.sqrt 3) (Real.sqrt 6) (Real.sqrt 3)
    halfGraphRow_bounded halfGraphParameter_bounded
    halfGraph_successiveLimit_sqrtSix
    halfGraph_reverse_successiveLimit_sqrtThree
  exact (ne_of_gt HalfGraph.sqrtThree_lt_sqrtSix) heq

end

end NormFormula.HalfGraph.Y
