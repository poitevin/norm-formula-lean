import NormFormula.Combinatorics.ElementaryThresholdTrace

/-!
# Constant and variable parts of the sparse affine lists

Distinct labels enumerate distinct coordinates in the two copies. Each
admissible pair therefore uses at most two distinct labels. Its constant
part is the sum of one row coordinate from each copy, allowing zero.
-/

namespace NormFormula.HalfGraph

def DistinctCoordinateLabels {ℓ : ℕ}
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ) : Prop :=
  Function.Injective fun a ↦ (copy a, index a)

def coordinateLabels {ℓ : ℕ} (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (target : CoordinateCopy) (n : ℕ) : Finset (Fin ℓ) :=
  Finset.univ.filter fun a ↦ copy a = target ∧ index a = n

theorem card_coordinateLabels_le_one {ℓ : ℕ}
    {copy : Fin ℓ → CoordinateCopy} {index : Fin ℓ → ℕ}
    (hdist : DistinctCoordinateLabels copy index) (target : CoordinateCopy) (n : ℕ) :
    (coordinateLabels copy index target n).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  exact hdist (Prod.ext (ha'.1.trans hb'.1.symm) (ha'.2.trans hb'.2.symm))

theorem coordinateLabels_disjoint {ℓ : ℕ}
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ) (a b : ℕ) :
    Disjoint (coordinateLabels copy index .first a) (coordinateLabels copy index .second b) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hi' := (Finset.mem_filter.mp hi).2.1
  have hj' := (Finset.mem_filter.mp hj).2.1
  exact CoordinateCopy.noConfusion (hi'.symm.trans hj')

theorem labelledCoordinateForm_eval_sum {ℓ : ℕ}
    (row : ℕ → ℝ) (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (target : CoordinateCopy) (n : ℕ) (t : Fin ℓ → ℝ) :
    (labelledCoordinateForm row copy index target n).eval t =
      row n + ∑ a ∈ coordinateLabels copy index target n, t a := by
  rw [labelledCoordinateForm_eval]
  simp [coordinateLabels, Finset.sum_filter]

noncomputable def rowCoordinateValues (row : ℕ → ℝ) (support : Finset ℕ) : Finset ℝ :=
  insert 0 (support.image row)

theorem mem_rowCoordinateValues (row : ℕ → ℝ) (support : Finset ℕ)
    (hrow : ∀ n, n ∉ support → row n = 0) (n : ℕ) :
    row n ∈ rowCoordinateValues row support := by
  classical
  by_cases hn : n ∈ support
  · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
  · rw [hrow n hn]
    exact Finset.mem_insert_self _ _

noncomputable def rowConstantSums (rowU rowV : ℕ → ℝ) (A B : Finset ℕ) : Finset ℝ :=
  ((rowCoordinateValues rowU A) ×ˢ (rowCoordinateValues rowV B)).image
    (fun p ↦ p.1 + p.2)

theorem mem_rowConstantSums {rowU rowV : ℕ → ℝ} {A B : Finset ℕ} {α β : ℝ}
    (hα : α ∈ rowCoordinateValues rowU A) (hβ : β ∈ rowCoordinateValues rowV B) :
    α + β ∈ rowConstantSums rowU rowV A B := by
  classical
  exact Finset.mem_image.mpr ⟨(α, β), Finset.mem_product.mpr ⟨hα, hβ⟩, rfl⟩

theorem card_rowConstantSums_le (rowU rowV : ℕ → ℝ) (A B : Finset ℕ) (m : ℕ)
    (hsize : A.card + B.card ≤ m) :
    (rowConstantSums rowU rowV A B).card ≤ (m + 1) ^ 2 := by
  classical
  have hA : (rowCoordinateValues rowU A).card ≤ m + 1 :=
    (Finset.card_insert_le _ _).trans (by have := Finset.card_image_le (s := A) (f := rowU); omega)
  have hB : (rowCoordinateValues rowV B).card ≤ m + 1 :=
    (Finset.card_insert_le _ _).trans (by have := Finset.card_image_le (s := B) (f := rowV); omega)
  calc
    _ ≤ ((rowCoordinateValues rowU A) ×ˢ (rowCoordinateValues rowV B)).card := Finset.card_image_le
    _ = (rowCoordinateValues rowU A).card * (rowCoordinateValues rowV B).card := Finset.card_product _ _
    _ ≤ (m + 1) * (m + 1) := Nat.mul_le_mul hA hB
    _ = (m + 1) ^ 2 := by ring

theorem symbolicAffineQForm_elementary {ℓ : ℕ}
    (rowU rowV : ℕ → ℝ) (A B : Finset ℕ)
    (copy : Fin ℓ → CoordinateCopy) (index : Fin ℓ → ℕ)
    (hdist : DistinctCoordinateLabels copy index)
    (hU : ∀ n, n ∉ A → rowU n = 0) (hV : ∀ n, n ∉ B → rowV n = 0)
    (f : AffineForm ℓ) (hf : f ∈ symbolicAffineQForms rowU rowV A B copy index) :
    ∃ α ∈ rowConstantSums rowU rowV A B, ∃ s : Finset (Fin ℓ),
      s.card ≤ 2 ∧ ∀ t, f.eval t = α + ∑ a ∈ s, t a := by
  classical
  have hzeroU : 0 ∈ rowCoordinateValues rowU A := Finset.mem_insert_self _ _
  have hzeroV : 0 ∈ rowCoordinateValues rowV B := Finset.mem_insert_self _ _
  rw [symbolicAffineQForms_eq_finiteAffineQForms, finiteAffineQForms] at hf
  rcases Finset.mem_insert.mp hf with rfl | hf
  · refine ⟨0, ?_, ∅, by simp, by simp⟩
    simpa using mem_rowConstantSums hzeroU hzeroV
  rcases Finset.mem_union.mp hf with hf | hf
  · rcases Finset.mem_union.mp hf with hf | hf
    · obtain ⟨a, ha, hf⟩ := Finset.mem_biUnion.mp hf
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hf
      refine ⟨rowU a + rowV b, mem_rowConstantSums
        (mem_rowCoordinateValues rowU A hU a) (mem_rowCoordinateValues rowV B hV b),
        coordinateLabels copy index .first a ∪ coordinateLabels copy index .second b, ?_, ?_⟩
      · have hcard := Finset.card_union_le (coordinateLabels copy index .first a)
          (coordinateLabels copy index .second b)
        have := card_coordinateLabels_le_one hdist .first a
        have := card_coordinateLabels_le_one hdist .second b
        omega
      · intro t
        rw [AffineForm.eval_add, labelledCoordinateForm_eval_sum, labelledCoordinateForm_eval_sum,
          Finset.sum_union (coordinateLabels_disjoint copy index a b)]
        ring
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hf
      refine ⟨rowU a, ?_, coordinateLabels copy index .first a,
        (card_coordinateLabels_le_one hdist .first a).trans (by omega), ?_⟩
      · simpa using mem_rowConstantSums (mem_rowCoordinateValues rowU A hU a) hzeroV
      · exact labelledCoordinateForm_eval_sum rowU copy index .first a
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hf
    refine ⟨rowV b, ?_, coordinateLabels copy index .second b,
      (card_coordinateLabels_le_one hdist .second b).trans (by omega), ?_⟩
    · simpa using mem_rowConstantSums hzeroU (mem_rowCoordinateValues rowV B hV b)
    · exact labelledCoordinateForm_eval_sum rowV copy index .second b

end NormFormula.HalfGraph
