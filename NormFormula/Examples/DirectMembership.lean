import NormFormula.Analytic.SeminormRenorm
import NormFormula.Analytic.Separability
import NormFormula.Analytic.HilbertNoC0
import NormFormula.Examples.HalfGraph
import NormFormula.ModelTheory.SeparableIPModel
import NormFormula.Analytic.MidpointUniformConvex
import Mathlib.Logic.Equiv.Finset

/-! # The direct membership space

The second copy of `ℓ₂` is reindexed by finite subsets through the explicit
bijection `code`. Thus the Hilbert basis has labels `ℕ ⊕ Finset ℕ`, and the
seminorm is exactly `sup_{i ∈ F} (|z(f_i)| + |z(e_F)|)`.
-/
namespace NormFormula.DirectMembership
noncomputable section
open HalfGraph
open scoped NNReal

def code : Finset ℕ ≃ ℕ := Denumerable.eqv _
abbrev Pair := {a : ℕ × Finset ℕ // a.1 ∈ a.2}
instance : Nonempty Pair := ⟨⟨(0,{0}), by simp⟩⟩

def pairSeminorm (i : ℕ) (F : Finset ℕ) : Seminorm ℝ HilbertSpace :=
  Seminorm.of (fun z ↦ |z.fst i| + |z.snd (code F)|)
    (fun x y ↦ by
      change |x.fst i+y.fst i| + |x.snd (code F)+y.snd (code F)| ≤ _
      nlinarith [abs_add_le (x.fst i) (y.fst i), abs_add_le (x.snd (code F)) (y.snd (code F))])
    (fun r x ↦ by
      change |r*x.fst i|+|r*x.snd (code F)| = ‖r‖*(|x.fst i|+|x.snd (code F)|)
      rw [abs_mul, abs_mul, Real.norm_eq_abs]; ring)

theorem pair_bound (i : ℕ) (F : Finset ℕ) (z : HilbertSpace) :
    pairSeminorm i F z ≤ Real.sqrt 2 * ‖z‖ := by
  have hx := lp.norm_apply_le_norm (by norm_num : (2:ENNReal) ≠ 0) z.fst i
  have hy := lp.norm_apply_le_norm (by norm_num : (2:ENNReal) ≠ 0) z.snd (code F)
  rw [Real.norm_eq_abs] at hx hy
  have hprod := WithLp.prod_norm_sq_eq_of_L2 z
  have hs : (Real.sqrt 2 * ‖z‖)^2 = 2*‖z‖^2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  change |z.fst i|+|z.snd (code F)| ≤ _
  nlinarith [norm_nonneg z.fst, norm_nonneg z.snd, abs_nonneg (z.fst i),
    abs_nonneg (z.snd (code F)), sq_nonneg (|z.fst i|-|z.snd (code F)|),
    mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg z)]

def admissible (a : Pair) := pairSeminorm a.1.1 a.1.2

theorem bdd : BddAbove (Set.range admissible) := by
  refine ⟨(2:ℝ≥0) • normSeminorm ℝ HilbertSpace, ?_⟩
  rintro _ ⟨a,rfl⟩ z
  change pairSeminorm a.1.1 a.1.2 z ≤ 2*‖z‖
  exact (pair_bound _ _ z).trans (mul_le_mul_of_nonneg_right
    (by rw [Real.sqrt_le_iff]; norm_num : Real.sqrt 2 ≤ 2) (norm_nonneg _))

def p : Seminorm ℝ HilbertSpace := ⨆ a : Pair, admissible a

theorem p_apply (z : HilbertSpace) :
    p z = ⨆ a : Pair, |z.fst a.1.1|+|z.snd (code a.1.2)| := by
  rw [p, Seminorm.iSup_apply bdd]
  rfl

theorem p_bound (z : HilbertSpace) : p z ≤ Real.sqrt 2 * ‖z‖ := by
  rw [p_apply]
  exact ciSup_le fun a ↦ pair_bound _ _ z

theorem p_sq_bound (z : HilbertSpace) : p z ^ 2 ≤ 2*‖z‖^2 := by
  have h := (sq_le_sq₀ (apply_nonneg p z)
    (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg z))).mpr (p_bound z)
  simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] using h

theorem pair_le (a : Pair) (z : HilbertSpace) : admissible a z ≤ p z :=
  (le_ciSup (f := admissible) bdd a) z

def row (i : ℕ) : HilbertSpace := xVector i
def parameter (F : Finset ℕ) : HilbertSpace := yVector (code F)

theorem pair_row_add (j i : ℕ) (T F : Finset ℕ) :
    pairSeminorm j T (row i + parameter F) =
      (if i=j then 1 else 0) + (if F=T then 1 else 0) := by
  change |(row i+parameter F).fst j|+|(row i+parameter F).snd (code T)| = _
  simp [row, parameter, basisVector_apply]
  split_ifs <;> norm_num

theorem p_row_add (i : ℕ) (F : Finset ℕ) :
    p (row i + parameter F) = if i ∈ F then 2 else 1 := by
  classical
  apply le_antisymm
  · rw [p, Seminorm.iSup_apply bdd]
    apply ciSup_le
    intro a
    change pairSeminorm _ _ _ ≤ _
    rw [pair_row_add]
    by_cases hi : i ∈ F
    · simp only [if_pos hi]
      split_ifs <;> norm_num
    · have hboth : ¬ (i=a.1.1 ∧ F=a.1.2) := by
        rintro ⟨rfl,rfl⟩
        exact hi a.2
      simp only [if_neg hi]
      split_ifs <;> simp_all
  · by_cases hi : i ∈ F
    · rw [if_pos hi]
      have h := pair_le ⟨(i,F),hi⟩ (row i + parameter F)
      simpa [admissible, pair_row_add, show (1:ℝ)+1=2 by norm_num] using h
    · rw [if_neg hi]
      have h := pair_le ⟨(i,{i}),by simp⟩ (row i + parameter F)
      have hF : F ≠ {i} := by intro hF; exact hi (by simp [hF])
      simpa [admissible, pair_row_add, hF] using h

theorem p_row (i : ℕ) : p (row i) ≤ 1 := by
  rw [p_apply]
  apply ciSup_le
  intro a
  change |basisVector i a.1.1| + |(0:ℝ)| ≤ 1
  simp only [basisVector_apply]
  split_ifs <;> norm_num

theorem p_parameter (F : Finset ℕ) : p (parameter F) ≤ 1 := by
  rw [p_apply]
  apply ciSup_le
  intro a
  change |(0:ℝ)| + |basisVector (code F) (code a.1.2)| ≤ 1
  simp only [basisVector_apply]
  split_ifs <;> norm_num

abbrev Space := AugmentedSpace p

def hilbertEquiv : Space ≃L[ℝ] HilbertSpace :=
  SeminormRenorm.continuousLinearEquiv _ _ (Real.sqrt 3)
    (augmentedNorm_le_sqrtThree_mul p p_sq_bound)
instance : CompleteSpace Space := SeminormRenorm.completeSpace _ _ (Real.sqrt 3)
  (augmentedNorm_le_sqrtThree_mul p p_sq_bound)
instance : TopologicalSpace.SeparableSpace Space := SeminormRenorm.separableSpace _ _ (Real.sqrt 3)
  (augmentedNorm_le_sqrtThree_mul p p_sq_bound)

def rowInSpace (i : ℕ) : Space := ⟨row i⟩
def parameterInSpace (F : Finset ℕ) : Space := ⟨parameter F⟩

theorem row_bound (i : ℕ) : ‖rowInSpace i‖ ≤ Real.sqrt 2 := by
  change augmentedNorm p (row i) ≤ _
  rw [augmentedNorm]
  apply Real.sqrt_le_sqrt
  have h := p_row i
  have hn : ‖row i‖ = 1 := by simp [row,xVector]
  rw [hn]
  nlinarith [apply_nonneg p (row i)]

theorem parameter_bound (F : Finset ℕ) : ‖parameterInSpace F‖ ≤ Real.sqrt 2 := by
  change augmentedNorm p (parameter F) ≤ _
  rw [augmentedNorm]
  apply Real.sqrt_le_sqrt
  have h := p_parameter F
  have hn : ‖parameter F‖ = 1 := by simp [parameter,yVector]
  rw [hn]
  nlinarith [apply_nonneg p (parameter F)]

theorem norm_row_add_parameter (i : ℕ) (F : Finset ℕ) :
    ‖rowInSpace i+parameterInSpace F‖ = if i ∈ F then Real.sqrt 6 else Real.sqrt 3 := by
  change augmentedNorm p (row i+parameter F) = _
  rw [augmentedNorm, p_row_add, show ‖row i+parameter F‖^2=2 from norm_sq_x_add_y _ _]
  split_ifs <;> norm_num

theorem infiniteIP : HasBoundedInfiniteIPWitness (fun x y : Space ↦ ‖x+y‖)
    (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 6) := by
  refine ⟨rowInSpace, row_bound, ?_⟩
  intro A B hAB
  refine ⟨parameterInSpace B, parameter_bound B, ?_, ?_⟩
  · intro i hi
    change ‖rowInSpace i+parameterInSpace B‖ ≤ _
    simp [norm_row_add_parameter, Finset.disjoint_left.mp hAB hi]
  · intro i hi
    change _ ≤ ‖rowInSpace i+parameterInSpace B‖
    simp [norm_row_add_parameter, hi]

theorem midpoint {x y : Space} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖(1/2:ℝ) • (x+y)‖^2 ≤ 1-(1/12:ℝ)*‖x-y‖^2 :=
  augmentedNorm_midpoint_sq_le p p_sq_bound hx hy

instance : UniformConvexSpace Space := uniformConvexSpaceOfMidpointEstimate (fun _ _ ↦ midpoint)

theorem no_c0 : ¬ ContainsIsomorphicCopyOfC0 Space :=
  not_containsIsomorphicCopyOfC0_of_equiv_innerProduct hilbertEquiv (Real.sqrt 3)
    (Real.sqrt_pos.mpr (by norm_num)) (augmentedNorm_le_sqrtThree_mul p p_sq_bound)
end
end NormFormula.DirectMembership
