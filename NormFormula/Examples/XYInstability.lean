import Mathlib.Topology.Sequences
import NormFormula.Analytic.XYSpace
import NormFormula.Examples.HalfGraph
import NormFormula.ModelTheory.BoundedStability

/-!
# Instability of the norm on `X ⊕₂ Y`

The second coordinate embedding transfers the paper's exact half-graph in
`Y` to the direct sum.  Its two successive limits are `√6` and `√3`,
which gives a direct, syntax-free proof that norm translation is not stable
on bounded sets.
-/

namespace NormFormula.XY

noncomputable section

open Filter
open scoped Topology

/-- The norm-translation predicate on the direct sum. -/
def normTranslate (u v : XYSpace) : ℝ := ‖u + v‖

/-- The row sequence of the half-graph, embedded in the `Y` summand. -/
def halfGraphRow (i : ℕ) : XYSpace := inY (HalfGraph.xInY i)

/-- The parameter sequence of the half-graph, embedded in the `Y` summand. -/
def halfGraphParameter (j : ℕ) : XYSpace := inY (HalfGraph.yInY j)

/-- The direct sum contains exactly the same two-valued half-graph as `Y`. -/
theorem normTranslate_halfGraph (i j : ℕ) :
    normTranslate (halfGraphRow i) (halfGraphParameter j) =
      if i < j then Real.sqrt 6 else Real.sqrt 3 := by
  rw [normTranslate, halfGraphRow, halfGraphParameter, ← inY_add, norm_inY]
  exact HalfGraph.norm_xInY_add_yInY i j

/-- The embedded row sequence lies in a fixed norm ball. -/
theorem halfGraphRow_bounded (i : ℕ) :
    ‖halfGraphRow i‖ ≤ Real.sqrt 3 := by
  rw [halfGraphRow, norm_inY]
  calc
    ‖HalfGraph.xInY i‖ ≤
        Real.sqrt 3 * ‖(HalfGraph.xInY i).toHilbert‖ :=
      HalfGraph.Y.norm_le_sqrtThree_mul_hilbert_norm _
    _ = Real.sqrt 3 := by simp [HalfGraph.xVector]

/-- The embedded parameter sequence lies in a fixed norm ball. -/
theorem halfGraphParameter_bounded (j : ℕ) :
    ‖halfGraphParameter j‖ ≤ Real.sqrt 3 := by
  rw [halfGraphParameter, norm_inY]
  calc
    ‖HalfGraph.yInY j‖ ≤
        Real.sqrt 3 * ‖(HalfGraph.yInY j).toHilbert‖ :=
      HalfGraph.Y.norm_le_sqrtThree_mul_hilbert_norm _
    _ = Real.sqrt 3 := by simp [HalfGraph.yVector]

/-- Taking the parameter limit first makes the half-graph converge successively to `√6`. -/
theorem halfGraph_successiveLimit_sqrtSix :
    HasSuccessiveLimit
      (fun i j ↦ normTranslate (halfGraphRow i) (halfGraphParameter j))
      (Real.sqrt 6) := by
  refine ⟨fun _ ↦ Real.sqrt 6, ?_, tendsto_const_nhds⟩
  intro i
  rw [show (fun j ↦ normTranslate (halfGraphRow i) (halfGraphParameter j)) =
      fun j ↦ if i < j then Real.sqrt 6 else Real.sqrt 3 by
        funext j
        exact normTranslate_halfGraph i j]
  refine (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [eventually_gt_atTop i] with j hij
  simp [hij]

/-- Reversing the order makes the half-graph converge successively to `√3`. -/
theorem halfGraph_reverse_successiveLimit_sqrtThree :
    HasSuccessiveLimit
      (fun j i ↦ normTranslate (halfGraphRow i) (halfGraphParameter j))
      (Real.sqrt 3) := by
  refine ⟨fun _ ↦ Real.sqrt 3, ?_, tendsto_const_nhds⟩
  intro j
  rw [show (fun i ↦ normTranslate (halfGraphRow i) (halfGraphParameter j)) =
      fun i ↦ if i < j then Real.sqrt 6 else Real.sqrt 3 by
        funext i
        exact normTranslate_halfGraph i j]
  refine (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [eventually_ge_atTop j] with i hji
  simp [Nat.not_lt.mpr hji]

/-- The norm formula is unstable on the concrete direct sum `X ⊕₂ Y`. -/
theorem normTranslate_not_isStableOnBounded :
    ¬ IsStableOnBounded normTranslate := by
  intro hstable
  have heq := hstable halfGraphRow halfGraphParameter
    (Real.sqrt 3) (Real.sqrt 3) (Real.sqrt 6) (Real.sqrt 3)
    halfGraphRow_bounded halfGraphParameter_bounded
    halfGraph_successiveLimit_sqrtSix halfGraph_reverse_successiveLimit_sqrtThree
  exact (ne_of_gt HalfGraph.sqrtThree_lt_sqrtSix) heq

end

end NormFormula.XY
