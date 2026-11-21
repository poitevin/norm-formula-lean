import NormFormula.Analytic.XWeakCompactness
import NormFormula.ModelTheory.SequentialLocalNIP
import NormFormula.ModelTheory.XStability

/-!
# The sequential norm-formula property on `X`

The weak sequential compactness proof used for stability yields a more direct
factor input for the later sum argument.  After passing to a weakly convergent
subsequence and then refining so that the norms of the differences converge,
the asymptotic Pythagoras theorem makes every norm translate converge along
the same subsequence.
-/

namespace NormFormula.X

noncomputable section

open Filter
open scoped Topology

/-- Every bounded sequence in `XSpace` has one subsequence along which
`x ↦ ‖x + y‖` converges for every home parameter `y : XSpace`. -/
theorem normTranslate_hasPointwiseConvergentSubsequenceOnBounded :
    NormFormula.HasPointwiseConvergentSubsequenceOnBounded normTranslate := by
  intro rows C hrows
  obtain ⟨x, subsequence, differenceLimit, hsubsequence, hweak,
      hnorm, hbound⟩ :=
    weakSequentialCompactnessOnBounded.exists_prepared_subsequence
      rows C hrows
  refine ⟨subsequence, hsubsequence, ?_⟩
  intro parameter
  refine ⟨Real.sqrt (‖parameter + x‖ ^ 2 + differenceLimit ^ 2), ?_⟩
  have hconverges := tendsto_norm_add_of_weaklyTendsto
    parameter hweak hbound hnorm
  simpa [normTranslate, add_comm] using hconverges

end


end NormFormula.X
