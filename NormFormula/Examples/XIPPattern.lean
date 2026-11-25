import NormFormula.Analytic.XSpace
import NormFormula.ModelTheory.LocalNIP

/-!
# Fixed-gap finite IP patterns in `X`

The cube vectors in the `n`th summand of `X` give an IP pattern of dimension
`n` with bounds and thresholds independent of `n`.  This is the constructive
premise used by continuous compactness to obtain IP in `Th(X)`.

It is important that this file only asserts finite patterns in every
dimension.  It does not identify them with an infinite IP witness inside the
distinguished space `X`.
-/

namespace NormFormula.X

noncomputable section

/-- Translation followed by the actual norm on `X`. -/
def normTranslate (x y : XSpace) : ℝ := ‖x + y‖

/-- The two cube levels have a fixed positive gap. -/
theorem sqrtThree_lt_sqrtSix : Real.sqrt 3 < Real.sqrt 6 :=
  Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- In dimension `n`, the rows in the `n`th block and the subset parameters
form the required fixed-gap IP pattern.  The parameter subtype records the
uniform `sqrt 2` ball bound directly. -/
theorem normTranslate_IPPattern (n : ℕ) :
    NormFormula.IsIPPattern
      (NormFormula.boundedBinaryValue normTranslate
        (fun i : Fin n ↦ rowInX i) (Real.sqrt 2))
      (Real.sqrt 3) (Real.sqrt 6) := by
  intro S
  let b : NormFormula.ClosedNormBall XSpace (Real.sqrt 2) :=
    ⟨subsetInX S, norm_subsetInX_le_sqrtTwo S⟩
  refine ⟨b, ?_, ?_⟩
  · intro i hi
    change Real.sqrt 6 ≤ ‖rowInX i + subsetInX S‖
    rw [norm_rowInX_add_subsetInX]
    simp [hi]
  · intro i hi
    change ‖rowInX i + subsetInX S‖ ≤ Real.sqrt 3
    rw [norm_rowInX_add_subsetInX]
    simp [hi]

/-- The norm translation predicate has bounded fixed-gap IP patterns in every
finite dimension, with all radii and levels independent of the dimension. -/
theorem normTranslate_hasIPPatternsInEveryDimension :
    NormFormula.HasIPPatternsInEveryDimension normTranslate
      (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 6) := by
  intro n
  refine ⟨fun i : Fin n ↦ rowInX i, ?_, normTranslate_IPPattern n⟩
  intro i
  rw [norm_rowInX]


end

end NormFormula.X
