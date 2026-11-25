import NormFormula.ContinuousLogic.BanachBallCompactness
import NormFormula.ContinuousLogic.BanachBallSeparableIP
import NormFormula.Analytic.Separability
import NormFormula.ContinuousLogic.XHilbertBallDirectedUnion
import NormFormula.Examples.XIPPattern

/-!
# Finite IP patterns for norm addition in the typed ball language

Both variables are placed in the rational radius-`2` sort, which contains the
existing cube rows and subset parameters of norm at most `√2`.  The sum term
has radius `4`, so its normalized distance-to-zero value is `‖x+y‖/8`.
-/

namespace NormFormula.X.BallLanguage

noncomputable section

open NormFormula.ContinuousLogic
open Set TopologicalSpace

universe u

/-- The typed norm-addition formula on two radius-`2` variables. -/
def normAddBallFormula :
    BallFormula PredicateSymbol predicateRadius
      (![(2 : ℚ≥0), (2 : ℚ≥0)] : BallContext 2) :=
  ambientNormFormula (BallTerm.binaryAddTerm 2 2)

/-- Concrete evaluation of the normalized typed norm-addition formula. -/
theorem normAddBallFormula_value
    (assignment : BallTerm.Assignment
      expansionStructure.toRationalBallSystem
      (![(2 : ℚ≥0), (2 : ℚ≥0)] : BallContext 2)) :
    (normAddBallFormula.realize expansionStructure assignment : ℝ) =
      ‖(assignment 0).1 + (assignment 1).1‖ / 8 := by
  unfold normAddBallFormula
  rw [ambientNormFormula_value]
  rw [BallTerm.binaryAddTerm_standardValue]
  norm_num [rationalBallMetricBound]


/-- In every same-theory ball model, the normalized norm-addition formula is
exactly the reconstructed distance of the sum from zero, divided by the
radius-`4` language scale. -/
theorem normAddBallFormula_completedDistance
    (A : XBallTheoryModel.{u})
    (x y : A.model.Ball 2) :
    dist
        (A.ballToCompletedDirectedPoint 2 x +
          A.ballToCompletedDirectedPoint 2 y)
        0 =
      rationalBallMetricBound 4 *
        normAddBallFormula.binaryValue A.model x y := by
  rw [← A.ballToCompletedDirectedPoint_add 2 2 x y,
    ← A.ballToCompletedDirectedPoint_zero ((2 : ℚ≥0) + 2)]
  rw [A.dist_ballToCompletedDirectedPoint]
  change rationalBallMetricBound ((2 : ℚ≥0) + 2) *
      (dist (A.model.add 2 2 (x, y)) (A.model.zero (2 + 2)) /
        A.model.sortBound (2 + 2)) =
    rationalBallMetricBound 4 *
      (dist (A.model.add 2 2 (x, y)) (A.model.zero (2 + 2)) /
        A.model.sortBound (2 + 2))
  norm_num [rationalBallMetricBound]

/-- On canonical points from the typed unit sort, the ambient sum formula is
exactly the reconstructed norm divided by the radius-`2` language scale. -/
theorem ambientAddUnitFormula_completedNorm
    (A : XBallTheoryModel.{u})
    (x y : A.model.Ball (1 : ℚ≥0)) :
    ‖A.ballToCompletedDirectedPoint 1 x +
        A.ballToCompletedDirectedPoint 1 y‖ =
      rationalBallMetricBound 2 *
        (ambientAddUnitFormula.realize A.model
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) : ℝ) := by
  rw [A.norm_completedDirectedPoint, dist_comm,
    ← A.ballToCompletedDirectedPoint_add 1 1 x y,
    ← A.ballToCompletedDirectedPoint_zero ((1 : ℚ≥0) + 1),
    A.dist_ballToCompletedDirectedPoint]
  change rationalBallMetricBound ((1 : ℚ≥0) + 1) *
      (dist (A.model.add 1 1 (x, y)) (A.model.zero (1 + 1)) /
        A.model.sortBound (1 + 1)) =
    rationalBallMetricBound 2 *
      (dist (A.model.add 1 1 (x, y)) (A.model.zero (1 + 1)) /
        A.model.sortBound (1 + 1))
  norm_num

/-- On canonical points from the typed unit sort, the ambient difference
formula is exactly the reconstructed norm divided by the radius-`2` language
scale. -/
theorem ambientSubUnitFormula_completedNorm
    (A : XBallTheoryModel.{u})
    (x y : A.model.Ball (1 : ℚ≥0)) :
    ‖A.ballToCompletedDirectedPoint 1 x -
        A.ballToCompletedDirectedPoint 1 y‖ =
      rationalBallMetricBound 2 *
        (ambientSubUnitFormula.realize A.model
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) : ℝ) := by
  rw [sub_eq_add_neg, ← A.ballToCompletedDirectedPoint_neg 1 y,
    A.norm_completedDirectedPoint, dist_comm,
    ← A.ballToCompletedDirectedPoint_add 1 1 x (A.model.neg 1 y),
    ← A.ballToCompletedDirectedPoint_zero ((1 : ℚ≥0) + 1),
    A.dist_ballToCompletedDirectedPoint]
  change rationalBallMetricBound ((1 : ℚ≥0) + 1) *
      (dist (A.model.add 1 1 (x, A.model.neg 1 y))
          (A.model.zero (1 + 1)) /
        A.model.sortBound (1 + 1)) =
    rationalBallMetricBound 2 *
      (dist (A.model.add 1 1 (x, A.model.neg 1 y))
          (A.model.zero (1 + 1)) /
        A.model.sortBound (1 + 1))
  norm_num

/-- The syntax-transferred midpoint estimate, unnormalized on the canonical
image of the typed unit sort in the reconstructed Banach space.  Extending
this theorem to all reconstructed vectors of norm at most one requires a
separate small-sort coverage or density theorem. -/
theorem midpoint_completedNorm_of_typedUnit
    (A : XBallTheoryModel.{u})
    (x y : A.model.Ball (1 : ℚ≥0)) :
    ‖(1 / 2 : ℝ) •
        (A.ballToCompletedDirectedPoint 1 x +
          A.ballToCompletedDirectedPoint 1 y)‖ ^ 2 ≤
      1 - (1 / 12 : ℝ) *
        ‖A.ballToCompletedDirectedPoint 1 x -
          A.ballToCompletedDirectedPoint 1 y‖ ^ 2 := by
  have hmid := midpoint_of_sameCompleteTheory A.model
    A.sameCompleteTheory x y
  have hadd := ambientAddUnitFormula_completedNorm A x y
  have hsub := ambientSubUnitFormula_completedNorm A x y
  have hscale : rationalBallMetricBound 2 = 4 := by
    norm_num [rationalBallMetricBound]
  rw [hscale] at hadd hsub
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [hadd, hsub]
  norm_num at hmid ⊢
  have hrearranged := (le_sub_iff_add_le).2 hmid
  convert hrearranged using 1 <;> ring_nf <;> rfl

/-- The midpoint sentence itself recovers the sharp semantic norm bound on
the canonical image of the typed unit sort. -/
theorem norm_ballToCompletedDirectedPoint_unit_le_one
    (A : XBallTheoryModel.{u}) (x : A.model.Ball (1 : ℚ≥0)) :
    ‖A.ballToCompletedDirectedPoint 1 x‖ ≤ 1 := by
  have hmid := midpoint_completedNorm_of_typedUnit A x x
  have haverage :
      (1 / 2 : ℝ) •
          (A.ballToCompletedDirectedPoint 1 x +
            A.ballToCompletedDirectedPoint 1 x) =
        A.ballToCompletedDirectedPoint 1 x := by
    module
  rw [haverage, sub_self, norm_zero] at hmid
  ring_nf at hmid
  nlinarith [norm_nonneg (A.ballToCompletedDirectedPoint 1 x)]

/-- A fixed-ball infinite distance-addition witness in the reconstructed
completed one-sorted carrier. -/
def XBallTheoryModel.HasCompletedDistanceAddWitness
    (A : XBallTheoryModel.{u}) (pointBound low high : ℝ) : Prop :=
  ∃ rows : ℕ → A.CompletedDirectedPoint,
    (∀ i, dist (rows i) 0 ≤ pointBound) ∧
    ∀ E F : Finset ℕ, Disjoint E F →
      ∃ parameter : A.CompletedDirectedPoint,
        dist parameter 0 ≤ pointBound ∧
        (∀ i ∈ E, dist (rows i + parameter) 0 ≤ low) ∧
        (∀ i ∈ F, high ≤ dist (rows i + parameter) 0)

/-- The corresponding literal norm-addition witness in the reconstructed
normed additive group. -/
def XBallTheoryModel.HasCompletedNormAddWitness
    (A : XBallTheoryModel.{u}) (pointBound low high : ℝ) : Prop :=
  ∃ rows : ℕ → A.CompletedDirectedPoint,
    (∀ i, ‖rows i‖ ≤ pointBound) ∧
    ∀ E F : Finset ℕ, Disjoint E F →
      ∃ parameter : A.CompletedDirectedPoint,
        ‖parameter‖ ≤ pointBound ∧
        (∀ i ∈ E, ‖rows i + parameter‖ ≤ low) ∧
        (∀ i ∈ F, high ≤ ‖rows i + parameter‖)

/-- Distance-addition and norm-addition witnesses are equivalent for the
canonical completed norm. -/
theorem XBallTheoryModel.hasCompletedDistanceAddWitness_iff_norm
    (A : XBallTheoryModel.{u}) (pointBound low high : ℝ) :
    A.HasCompletedDistanceAddWitness pointBound low high ↔
      A.HasCompletedNormAddWitness pointBound low high := by
  simp only [XBallTheoryModel.HasCompletedDistanceAddWitness,
    XBallTheoryModel.HasCompletedNormAddWitness,
    A.norm_completedDirectedPoint, dist_comm]

/-- Every typed radius-`2` norm-addition witness maps to a fixed-ball
distance-addition witness in the reconstructed completed carrier. -/
theorem normAddBallFormula_hasCompletedDistanceAddWitness
    (A : XBallTheoryModel.{u}) {low high : ℝ}
    (hIP : normAddBallFormula.HasInfiniteIPWitness A.model low high) :
    A.HasCompletedDistanceAddWitness
      (rationalBallMetricBound 2)
      (rationalBallMetricBound 4 * low)
      (rationalBallMetricBound 4 * high) := by
  obtain ⟨typedRows, htyped⟩ := hIP
  refine ⟨fun i ↦ A.ballToCompletedDirectedPoint 2 (typedRows i), ?_, ?_⟩
  · intro i
    exact A.dist_ballToCompletedDirectedPoint_zero_le 2 (typedRows i)
  · intro E F hdisjoint
    obtain ⟨typedParameter, hlow, hhigh⟩ := htyped E F hdisjoint
    refine ⟨A.ballToCompletedDirectedPoint 2 typedParameter,
      A.dist_ballToCompletedDirectedPoint_zero_le 2 typedParameter, ?_, ?_⟩
    · intro i hi
      rw [normAddBallFormula_completedDistance A]
      exact mul_le_mul_of_nonneg_left (hlow i hi)
        (rationalBallMetricBound_pos 4).le
    · intro i hi
      rw [normAddBallFormula_completedDistance A]
      exact mul_le_mul_of_nonneg_left (hhigh i hi)
        (rationalBallMetricBound_pos 4).le

/-- The existing cube construction gives uniformly normalized finite IP
patterns for the typed radius-`2` norm-addition formula. -/
theorem normAddBallFormula_hasFiniteIPPatternsInEveryDimension :
    normAddBallFormula.HasFiniteIPPatternsInEveryDimension
      expansionStructure (Real.sqrt 3 / 8) (Real.sqrt 6 / 8) := by
  have hsqrtTwo_le_two : Real.sqrt 2 ≤ 2 := by
    have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hsqrtNonneg := Real.sqrt_nonneg 2
    nlinarith
  intro n
  let rows : Fin n → expansionStructure.Ball 2 := fun i ↦
    ⟨rowInX i, by
      rw [norm_rowInX]
      exact hsqrtTwo_le_two⟩
  refine ⟨rows, ?_⟩
  intro subset
  obtain ⟨parameter, hhigh, hlow⟩ := normTranslate_IPPattern n subset
  let typedParameter : expansionStructure.Ball 2 :=
    ⟨parameter.1, parameter.2.trans hsqrtTwo_le_two⟩
  refine ⟨typedParameter, ?_, ?_⟩
  · intro i hi
    have h := hhigh i hi
    change Real.sqrt 6 / 8 ≤
      normAddBallFormula.binaryValue expansionStructure (rows i)
        typedParameter
    rw [BallFormula.binaryValue, normAddBallFormula_value]
    exact div_le_div_of_nonneg_right h (by norm_num)
  · intro i hi
    have h := hlow i hi
    change normAddBallFormula.binaryValue expansionStructure (rows i)
        typedParameter ≤ Real.sqrt 3 / 8
    rw [BallFormula.binaryValue, normAddBallFormula_value]
    exact div_le_div_of_nonneg_right h (by norm_num)


/-- The retained copy of the original expanded `X` in the typed model.
The sort maps preserve terms and all formula values on original tuples. -/
structure XBallElementaryCopy (A : XBallTheoryModel.{0}) where
  map : ∀ radius, expansionStructure.Ball radius → A.model.Ball radius
  realize_term : ∀ {n : ℕ} {context : BallContext n} {r : ℚ≥0}
    (term : BallTerm context r)
    (assignment : BallTerm.Assignment expansionStructure.toRationalBallSystem context),
    term.realize A.model.toRationalBallSystem (fun i ↦ map (context i) (assignment i)) =
      map r (term.realize expansionStructure.toRationalBallSystem assignment)
  realize_formula : ∀ {n : ℕ} {context : BallContext n}
    (formula : BallFormula PredicateSymbol predicateRadius context)
    (assignment : BallTerm.Assignment expansionStructure.toRationalBallSystem context),
    formula.realize A.model (fun i ↦ map (context i) (assignment i)) =
      formula.realize expansionStructure assignment

/-- In the ultrapower carrying the IP witness, seed the closed elementary
substructure with a dense sequence from each original ball of `X`.
Closedness then retains the whole diagonal copy. -/
theorem exists_sortwiseSeparable_normAddIPModel_with_copy :
    ∃ A : XBallTheoryModel.{0},
      Nonempty (XBallElementaryCopy A) ∧
      (∀ radius : ℚ≥0, IsSeparable (Set.univ : Set (A.model.Ball radius))) ∧
      normAddBallFormula.HasInfiniteIPWitness A.model
        (Real.sqrt 3 / 8) (Real.sqrt 6 / 8) := by
  let S := expansionStructure.toRationalBallSystem
  letI (r : ℚ≥0) : SeparableSpace (expansionStructure.Ball r) :=
    inferInstanceAs (SeparableSpace (RationalNormBall XSpace r))
  let seed (r : ℚ≥0) (k : ℕ) := S.reducedConst r (denseSeq (expansionStructure.Ball r) k)
  obtain ⟨initial, hseed, hIP⟩ :=
    BallFormula.exists_separableElementaryIPSubstructure_containing seed
      (BallFormula.hasInfiniteIPWitness_reducedProduct_of_finitePatterns
        expansionStructure normAddBallFormula (Real.sqrt 3 / 8) (Real.sqrt 6 / 8)
        normAddBallFormula_hasFiniteIPPatternsInEveryDimension)
  have hdiag (r : ℚ≥0) : LipschitzWith 1 (S.reducedConst r) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (ReducedProduct.completedConst (S.reducedBound r) x)
      (ReducedProduct.completedConst (S.reducedBound r) y) ≤ (1 : ℝ) * dist x y
    rw [ReducedProduct.completedConst, ReducedProduct.completedConst,
      UniformSpace.Completion.dist_eq, ReducedProduct.dist_const, one_mul]
    exact div_le_self (dist_nonneg (x := x) (y := y)) (le_max_left 1 (2 * (r : ℝ)))
  have hmem (r : ℚ≥0) (x : expansionStructure.Ball r) :
      S.reducedConst r x ∈ initial.LimitCarrier r :=
    (denseRange_denseSeq (α := expansionStructure.Ball r)).induction_on x
      (isClosed_closure.preimage (hdiag r).continuous) (hseed r)
  let A : XBallTheoryModel.{0} := ⟨initial.limitBallStructure, fun sentence ↦
    (ballSameCompleteTheory_reducedProduct expansionStructure sentence).trans
      (initial.limitBallStructure_sameCompleteTheory_ambient sentence).symm⟩
  let copy (r : ℚ≥0) (x : expansionStructure.Ball r) : A.model.Ball r :=
    ⟨S.reducedConst r x, hmem r x⟩
  refine ⟨A, ⟨⟨copy, ?_, ?_⟩⟩, initial.limitCarrier_isSeparable, hIP⟩
  · intro n context r term assignment
    apply Subtype.ext
    calc
      _ = term.realize S.reducedProduct
          (fun i ↦ S.reducedConst (context i) (assignment i)) :=
        initial.term_realize_limitBallStructure_eq_ambient term
          (fun i ↦ copy (context i) (assignment i))
      _ = _ := BallTerm.realize_reducedConst S term assignment
  · intro n context formula assignment
    exact (initial.ballFormula_realize_limitBallStructure_eq_ambient formula
      (fun i ↦ copy (context i) (assignment i))).trans
      (formula.realize_reducedConst expansionStructure assignment)

/-- The unconditional reconstruction packaged together with its constructed
separable auxiliary Hilbert space. The bundle records the elementary copy
of `X`, separability, and the IP witness. The Hilbert structure, completeness,
and quantitative continuous linear equivalence are constructed from `model`. -/
structure SeparableHilbertianNormAddIPModel where
  model : XBallTheoryModel.{0}
  elementaryCopy : XBallElementaryCopy model
  sortwiseSeparable : ∀ radius : ℚ≥0,
    IsSeparable (Set.univ : Set (model.model.Ball radius))
  completedSeparable : SeparableSpace model.CompletedDirectedPoint
  auxiliaryHilbertSeparable : SeparableSpace model.AuxiliaryHilbertCarrier
  typedNormAddWitness : normAddBallFormula.HasInfiniteIPWitness model.model
    (Real.sqrt 3 / 8) (Real.sqrt 6 / 8)
  normAddWitness : model.HasCompletedNormAddWitness
    4 (Real.sqrt 3) (Real.sqrt 6)

/-- The separable reconstruction retains the elementary copy of `X` and the
fixed-ball norm-addition IP witness. The auxiliary Hilbert norm on the same
space is complete and equivalent with constants `1` and `√3`. -/
theorem exists_separableHilbertian_normAddIPModel :
    Nonempty SeparableHilbertianNormAddIPModel := by
  obtain ⟨A, ⟨copy⟩, hsortwise, hIP⟩ := exists_sortwiseSeparable_normAddIPModel_with_copy
  have hwitness : A.HasCompletedDistanceAddWitness 4 (Real.sqrt 3) (Real.sqrt 6) := by
    convert normAddBallFormula_hasCompletedDistanceAddWitness A hIP using 1 <;>
      norm_num [rationalBallMetricBound] <;> ring
  exact ⟨{
    model := A
    elementaryCopy := copy
    sortwiseSeparable := hsortwise
    completedSeparable := A.completedDirectedPoint_separableSpace hsortwise
    auxiliaryHilbertSeparable :=
      A.auxiliaryHilbertCarrier_separableSpace hsortwise
    typedNormAddWitness := hIP
    normAddWitness := (A.hasCompletedDistanceAddWitness_iff_norm _ _ _).mp hwitness
  }⟩

end

end NormFormula.X.BallLanguage
