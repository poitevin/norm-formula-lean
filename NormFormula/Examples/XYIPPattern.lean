import NormFormula.Examples.XIPPattern
import NormFormula.Examples.XYInstability

/-!
# Fixed-gap finite IP patterns in `X ⊕₂ Y`

The isometric embedding of the first summand transfers the cube patterns from
`X` to the direct sum without changing their radii or their two norm values.
This is the constructive premise for IP in the complete theory of the sum.
-/

namespace NormFormula.XY

noncomputable section

/-- The `X`-cube rows, embedded in the first summand of the direct sum. -/
def cubeRow {n : ℕ} (i : Fin n) : XYSpace :=
  inX (X.rowInX i)

/-- A subset parameter from the `X`-cube, embedded in the first summand. -/
def cubeParameter {n : ℕ} (S : Finset (Fin n)) : XYSpace :=
  inX (X.subsetInX S)

@[simp]
theorem norm_cubeRow {n : ℕ} (i : Fin n) :
    ‖cubeRow i‖ = Real.sqrt 2 := by
  rw [cubeRow, norm_inX, X.norm_rowInX]

theorem norm_cubeParameter_le_sqrtTwo {n : ℕ} (S : Finset (Fin n)) :
    ‖cubeParameter S‖ ≤ Real.sqrt 2 := by
  rw [cubeParameter, norm_inX]
  exact X.norm_subsetInX_le_sqrtTwo S

/-- The exact two-valued cube computation is unchanged in the direct sum. -/
theorem normTranslate_cube (i : Fin n) (S : Finset (Fin n)) :
    normTranslate (cubeRow i) (cubeParameter S) =
      if i ∈ S then Real.sqrt 6 else Real.sqrt 3 := by
  rw [normTranslate, cubeRow, cubeParameter, ← inX_add, norm_inX]
  exact X.norm_rowInX_add_subsetInX i S

/-- In every dimension, the embedded cube gives a fixed-gap IP pattern in
the same `√2` balls as the original pattern in `X`. -/
theorem normTranslate_IPPattern (n : ℕ) :
    IsIPPattern
      (boundedBinaryValue normTranslate
        (fun i : Fin n ↦ cubeRow i) (Real.sqrt 2))
      (Real.sqrt 3) (Real.sqrt 6) := by
  intro S
  let b : ClosedNormBall XYSpace (Real.sqrt 2) :=
    ⟨cubeParameter S, norm_cubeParameter_le_sqrtTwo S⟩
  refine ⟨b, ?_, ?_⟩
  · intro i hi
    change Real.sqrt 6 ≤ normTranslate (cubeRow i) (cubeParameter S)
    rw [normTranslate_cube]
    simp [hi]
  · intro i hi
    change normTranslate (cubeRow i) (cubeParameter S) ≤ Real.sqrt 3
    rw [normTranslate_cube]
    simp [hi]

/-- Norm translation on `X ⊕₂ Y` has uniformly bounded, fixed-gap
patterns in every finite dimension. -/
theorem normTranslate_hasIPPatternsInEveryDimension :
    HasIPPatternsInEveryDimension normTranslate
      (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 6) := by
  intro n
  refine ⟨fun i : Fin n ↦ cubeRow i, ?_, normTranslate_IPPattern n⟩
  intro i
  rw [norm_cubeRow]


end

end NormFormula.XY
