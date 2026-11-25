import Mathlib.Topology.Instances.RealVectorSpace
import NormFormula.ContinuousLogic.XHilbertBallSmallSort
import NormFormula.ContinuousLogic.FullBanachBallTheoryIP

/-!
# The reconstructed X model as a standard predicate-free Banach-ball model

The directed-union reconstruction initially produces canonical maps from the
typed ball sorts into one completed Banach carrier.  This file proves that the
map from the radius-`r` sort lands in, and maps onto, the actual closed
radius-`r` ball of the completion.  These sharp all-radius statements are the
semantic input needed to identify the predicate-free reduct with the standard
Banach-ball structure of the reconstructed carrier.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u v w

/-- Forget all named predicates while retaining the complete rational-ball
operation system. -/
def BallStructure.predicateFreeReduct
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    (M : BallStructure.{v, w} Symbol symbolRadius) :
    BallStructure EmptyBallPredicate emptyBallPredicateRadius where
  toRationalBallSystem := M.toRationalBallSystem
  predicate := nofun
  predicate_uniformContinuous := nofun

namespace BallFormula

/-- Regard a predicate-free formula as a formula in any expansion of the
same rational-ball language. -/
def fromPredicateFree
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n} :
    BallFormula EmptyBallPredicate emptyBallPredicateRadius context →
      BallFormula Symbol symbolRadius context
  | .distance left right => .distance left right
  | .predicate symbol _term => nomatch symbol
  | .constant value => .constant value
  | .connective gate children =>
      .connective gate (fun i ↦ fromPredicateFree (children i))
  | .iSup radius formula => .iSup radius (fromPredicateFree formula)
  | .iInf radius formula => .iInf radius (fromPredicateFree formula)

/-- Forgetting predicates and then evaluating is the same as evaluating the
predicate-free formula in the reduct. -/
theorem realize_fromPredicateFree
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    (M : BallStructure.{v, w} Symbol symbolRadius)
    {n : ℕ} {context : BallContext n}
    (formula : BallFormula EmptyBallPredicate emptyBallPredicateRadius context)
    (assignment : BallTerm.Assignment M.toRationalBallSystem context) :
    formula.fromPredicateFree.realize M assignment =
      formula.realize M.predicateFreeReduct assignment := by
  induction formula with
  | distance left right => rfl
  | predicate symbol term => exact nomatch symbol
  | constant value => rfl
  | connective gate children induction =>
      change gate (fun i ↦ (children i).fromPredicateFree.realize M assignment) =
        gate (fun i ↦ (children i).realize M.predicateFreeReduct assignment)
      congr 1
      funext i
      exact induction i assignment
  | iSup radius formula induction =>
      change (⨆ x, formula.fromPredicateFree.realize M (Fin.cons x assignment)) =
        ⨆ x, formula.realize M.predicateFreeReduct (Fin.cons x assignment)
      congr 1
      funext x
      exact induction (Fin.cons x assignment)
  | iInf radius formula induction =>
      change (⨅ x, formula.fromPredicateFree.realize M (Fin.cons x assignment)) =
        ⨅ x, formula.realize M.predicateFreeReduct (Fin.cons x assignment)
      congr 1
      funext x
      exact induction (Fin.cons x assignment)

end BallFormula

/-- A real linear isometry is elementary when its maps on the standard
rational-radius sorts preserve every formula on every finite tuple. -/
def IsElementaryBanachEmbedding
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (e : E →ₗᵢ[ℝ] F) : Prop :=
  ∀ {n : ℕ} {context : BallContext n}
    (formula : BallFormula EmptyBallPredicate emptyBallPredicateRadius context)
    (assignment : BallTerm.Assignment (standardRationalBallSystem (E := E)) context),
    formula.realize (standardBanachBallStructure F)
        (fun i ↦ ⟨e (assignment i).1, by simpa only [e.norm_map] using (assignment i).2⟩) =
      formula.realize (standardBanachBallStructure E) assignment

namespace IsElementaryBanachEmbedding

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]

private def mapBall (e : E →ₗᵢ[ℝ] F) {r : ℚ≥0} (x : RationalNormBall E r) :
    RationalNormBall F r :=
  ⟨e x.1, by simpa only [e.norm_map] using x.2⟩

private def mapAssignment (e : E →ₗᵢ[ℝ] F) {n : ℕ} {context : BallContext n}
    (assignment : BallTerm.Assignment (standardRationalBallSystem (E := E)) context) :
    BallTerm.Assignment (standardRationalBallSystem (E := F)) context :=
  fun i ↦ mapBall e (assignment i)

private theorem mapAssignment_cons (e : E →ₗᵢ[ℝ] F) {n : ℕ} {context : BallContext n}
    {r : ℚ≥0} (x : RationalNormBall E r)
    (assignment : BallTerm.Assignment (standardRationalBallSystem (E := E)) context) :
    mapAssignment e (context := Fin.cons r context) (Fin.cons x assignment) =
      (Fin.cons (mapBall e x) (mapAssignment e assignment) :
        BallTerm.Assignment (standardRationalBallSystem (E := F)) (Fin.cons r context)) := by
  funext i
  exact Fin.cases rfl (fun _ ↦ rfl) i

private theorem standardValue_mapAssignment (e : E →ₗᵢ[ℝ] F)
    {n : ℕ} {context : BallContext n} {r : ℚ≥0} (term : BallTerm context r)
    (assignment : BallTerm.Assignment (standardRationalBallSystem (E := E)) context) :
    term.standardValue (mapAssignment e assignment) = e (term.standardValue assignment) := by
  induction term with
  | «variable» i => rfl
  | inclusion h term ih => simpa only [BallTerm.standardValue_inclusion] using ih
  | zero r => simp
  | neg term ih => simp only [BallTerm.standardValue_neg, ih, map_neg]
  | add left right ihLeft ihRight =>
      simp only [BallTerm.standardValue_add, ihLeft, ihRight, map_add]
  | smul q term ih => simp only [BallTerm.standardValue_smul, ih, map_smul]

/-- A surjective real linear isometry preserves all standard Banach-ball
formulas. On each radius sort, surjectivity permits a change of variable in
the interpretation of either quantifier. -/
theorem of_linearIsometryEquiv (e : E ≃ₗᵢ[ℝ] F) :
    IsElementaryBanachEmbedding e.toLinearIsometry := by
  let f := e.toLinearIsometry
  have hsurj (r : ℚ≥0) : Function.Surjective (mapBall f (r := r)) := by
    intro y
    refine ⟨⟨e.symm y.1, by simpa only [e.symm.norm_map] using y.2⟩, ?_⟩
    apply Subtype.ext
    exact e.apply_symm_apply y.1
  intro n context formula assignment
  change formula.realize (standardBanachBallStructure F) (mapAssignment f assignment) =
    formula.realize (standardBanachBallStructure E) assignment
  induction formula with
  | distance left right =>
      apply Subtype.ext
      change dist (left.standardValue (mapAssignment f assignment))
          (right.standardValue (mapAssignment f assignment)) / rationalBallMetricBound _ =
        dist (left.standardValue assignment) (right.standardValue assignment) /
          rationalBallMetricBound _
      rw [standardValue_mapAssignment, standardValue_mapAssignment, f.dist_map]
  | predicate symbol _ => exact nomatch symbol
  | constant _ => rfl
  | connective gate children ih =>
      change gate (fun i ↦ (children i).realize (standardBanachBallStructure F)
          (mapAssignment f assignment)) =
        gate (fun i ↦ (children i).realize (standardBanachBallStructure E) assignment)
      congr 1
      funext i
      exact ih i assignment
  | iSup r formula ih =>
      change (⨆ x : RationalNormBall F r,
          formula.realize (standardBanachBallStructure F)
            (Fin.cons x (mapAssignment f assignment))) =
        ⨆ x : RationalNormBall E r,
          formula.realize (standardBanachBallStructure E) (Fin.cons x assignment)
      rw [← (hsurj r).iSup_comp]
      congr 1
      funext x
      simpa only [mapAssignment_cons f x assignment] using ih (Fin.cons x assignment)
  | iInf r formula ih =>
      change (⨅ x : RationalNormBall F r,
          formula.realize (standardBanachBallStructure F)
            (Fin.cons x (mapAssignment f assignment))) =
        ⨅ x : RationalNormBall E r,
          formula.realize (standardBanachBallStructure E) (Fin.cons x assignment)
      rw [← (hsurj r).iInf_comp]
      congr 1
      funext x
      simpa only [mapAssignment_cons f x assignment] using ih (Fin.cons x assignment)

theorem comp {e : E →ₗᵢ[ℝ] F} {f : F →ₗᵢ[ℝ] G}
    (hf : IsElementaryBanachEmbedding f) (he : IsElementaryBanachEmbedding e) :
    IsElementaryBanachEmbedding (f.comp e) := by
  intro n context formula assignment
  exact (hf formula (mapAssignment e assignment)).trans (he formula assignment)

theorem sameCompleteTheory {e : E →ₗᵢ[ℝ] F} (he : IsElementaryBanachEmbedding e) :
    BallSameCompleteTheory (standardBanachBallStructure E) (standardBanachBallStructure F) := by
  intro sentence
  have h := he sentence (fun i : Fin 0 ↦ nomatch i)
  have hEmpty : mapAssignment e (context := Fin.elim0)
      (fun i : Fin 0 ↦ nomatch i) = (fun i : Fin 0 ↦ nomatch i) := Subsingleton.elim _ _
  change sentence.realize (standardBanachBallStructure F)
    (mapAssignment e (context := Fin.elim0) (fun i : Fin 0 ↦ nomatch i)) = _ at h
  rw [hEmpty] at h
  exact h.symm

end IsElementaryBanachEmbedding

/-- Equal complete theories remain equal after forgetting every named
predicate. -/
theorem BallSameCompleteTheory.predicateFreeReduct
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {M : BallStructure.{u, w} Symbol symbolRadius}
    {N : BallStructure.{v, w} Symbol symbolRadius}
    (hTheory : BallSameCompleteTheory M N) :
    BallSameCompleteTheory M.predicateFreeReduct N.predicateFreeReduct := by
  intro sentence
  have h := hTheory sentence.fromPredicateFree
  simpa only [BallSentence.value, BallFormula.realize_fromPredicateFree] using h

end

end NormFormula.ContinuousLogic

namespace NormFormula.X.BallLanguage

noncomputable section

open NormFormula.ContinuousLogic

universe u

namespace XBallTheoryModel

/-- Every canonical point from the typed radius-`r` sort has reconstructed
norm at most `r`. -/
theorem norm_ballToCompletedDirectedPoint_le_radius
    (A : XBallTheoryModel.{u}) (radius : ℚ≥0)
    (x : A.model.Ball radius) :
    ‖A.ballToCompletedDirectedPoint radius x‖ ≤ (radius : ℝ) := by
  by_cases hradius : radius = 0
  · subst radius
    have hzero : A.ballToCompletedDirectedPoint 0 x = 0 := by
      apply norm_eq_zero.mp
      apply le_antisymm
      · apply le_of_forall_pos_le_add
        intro ε hε
        obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (1 / ε)
        have hnpos : 0 < (n : ℝ) := by
          have : 0 < (1 / ε : ℝ) := one_div_pos.mpr hε
          exact lt_trans this hn
        have hscaled :
            ‖(n : ℚ) • A.ballToCompletedDirectedPoint 0 x‖ ≤ 1 := by
          rw [← A.ballToCompletedDirectedPoint_smul (n : ℚ) 0 x]
          have hinclude := norm_ballToCompletedDirectedPoint_unit_le_one A
            (A.model.inclusion (by norm_num) (A.model.smul (n : ℚ) 0 x))
          rwa [A.ballToCompletedDirectedPoint_inclusion] at hinclude
        rw [A.norm_completedSmul, ← Rat.norm_cast_real, Real.norm_eq_abs] at hscaled
        have hnnonneg : (0 : ℝ) ≤ (((n : ℕ) : ℚ) : ℝ) := by positivity
        have hncast : (((n : ℕ) : ℚ) : ℝ) = (n : ℝ) := by norm_cast
        rw [abs_of_nonneg hnnonneg, hncast] at hscaled
        have hnε : 1 < (n : ℝ) * ε := by
          calc
            1 = (1 / ε) * ε := by field_simp
            _ < (n : ℝ) * ε := mul_lt_mul_of_pos_right hn hε
        nlinarith [norm_nonneg (A.ballToCompletedDirectedPoint 0 x)]
      · exact norm_nonneg _
    simp [hzero]
  · have hradiusPos : (0 : ℚ≥0) < radius :=
      lt_of_le_of_ne radius.2 (Ne.symm hradius)
    let q : ℚ := ((radius : ℚ)⁻¹)
    have hqnnabs : q.nnabs * radius = 1 := by
      ext
      simp [q, hradius]
    have hle : q.nnabs * radius ≤ 1 := hqnnabs.le
    have hscaled := norm_ballToCompletedDirectedPoint_unit_le_one A
      (A.model.inclusion hle (A.model.smul q radius x))
    rw [A.ballToCompletedDirectedPoint_inclusion hle,
      A.ballToCompletedDirectedPoint_smul,
      A.norm_completedSmul, ← Rat.norm_cast_real,
      Real.norm_eq_abs, abs_of_pos] at hscaled
    · have hqReal : (q : ℝ) = ((radius : ℝ) : ℝ)⁻¹ := by
        norm_cast
      rw [hqReal] at hscaled
      simpa only [mul_one] using
        (inv_mul_le_iff₀ (by exact_mod_cast hradiusPos)).mp hscaled
    · exact_mod_cast (inv_pos.mpr (by exact_mod_cast hradiusPos : (0 : ℚ) < radius))

/-- The canonical map into the actual closed radius-`r` ball of the
reconstructed Banach carrier. -/
def ballToStandardNormBall (A : XBallTheoryModel.{u}) (radius : ℚ≥0) :
    A.model.Ball radius → RationalNormBall A.CompletedDirectedPoint radius :=
  fun x ↦ ⟨A.ballToCompletedDirectedPoint radius x,
    A.norm_ballToCompletedDirectedPoint_le_radius radius x⟩


/-- Every actual point of the reconstructed closed radius-`r` ball has an
exact representative in the corresponding typed sort. -/
theorem ballToStandardNormBall_surjective
    (A : XBallTheoryModel.{u}) (radius : ℚ≥0) :
    Function.Surjective (A.ballToStandardNormBall radius) := by
  intro p
  by_cases hradius : radius = 0
  · subst radius
    have hp : ‖p.1‖ ≤ (0 : ℝ) :=
      p.2.trans_eq NNRat.cast_zero
    have hpzero : (p : A.CompletedDirectedPoint) = 0 := by
      exact norm_eq_zero.mp
        (le_antisymm hp (norm_nonneg _))
    refine ⟨A.model.zero 0, Subtype.ext ?_⟩
    change A.ballToCompletedDirectedPoint 0 (A.model.zero 0) = p.1
    rw [A.ballToCompletedDirectedPoint_zero, hpzero]
  · have hradiusPos : (0 : ℚ≥0) < radius :=
      lt_of_le_of_ne radius.2 (Ne.symm hradius)
    let q : ℚ := ((radius : ℚ)⁻¹)
    have hscaled : ‖q • (p : A.CompletedDirectedPoint)‖ ≤ 1 := by
      rw [A.norm_completedSmul, ← Rat.norm_cast_real, Real.norm_eq_abs,
        abs_of_pos]
      · have hqReal : (q : ℝ) = ((radius : ℝ) : ℝ)⁻¹ := by
          norm_cast
        rw [hqReal]
        exact (inv_mul_le_one₀ (by exact_mod_cast hradiusPos)).2 p.2
      · exact_mod_cast (inv_pos.mpr (by exact_mod_cast hradiusPos : (0 : ℚ) < radius))
    obtain ⟨y, hy⟩ :=
      exists_unitBall_eq_of_completedNorm_le_one_global A (q • p.1) hscaled
    let scalar : ℚ := (radius : ℚ)
    have hscalarRadius : scalar.nnabs * 1 = radius := by
      ext
      simp [scalar]
    let z : A.model.Ball radius :=
      A.model.inclusion hscalarRadius.le (A.model.smul scalar 1 y)
    refine ⟨z, Subtype.ext ?_⟩
    change A.ballToCompletedDirectedPoint radius z = p.1
    have hz : A.ballToCompletedDirectedPoint radius z =
        scalar • A.ballToCompletedDirectedPoint 1 y := by
      dsimp [z]
      rw [A.ballToCompletedDirectedPoint_inclusion,
        A.ballToCompletedDirectedPoint_smul]
    rw [hz, hy]
    rw [← mul_smul]
    have hmul : scalar * q = 1 := by
      dsimp [scalar, q]
      field_simp
    rw [hmul, one_smul]

/-- Map a source assignment to the corresponding assignment in the standard
rational balls of the reconstructed completion. -/
def standardNormBallAssignment
    (A : XBallTheoryModel.{u}) {n : ℕ} {context : BallContext n}
    (assignment : BallTerm.Assignment A.model.toRationalBallSystem context) :
    BallTerm.Assignment
      (standardRationalBallSystem (E := A.CompletedDirectedPoint)) context :=
  fun i ↦ A.ballToStandardNormBall (context i) (assignment i)

@[simp]
theorem standardNormBallAssignment_cons
    (A : XBallTheoryModel.{u}) {n : ℕ} {context : BallContext n}
    (radius : ℚ≥0) (x : A.model.Ball radius)
    (assignment : BallTerm.Assignment A.model.toRationalBallSystem context) :
    A.standardNormBallAssignment (Fin.cons x assignment) =
      (Fin.cons (A.ballToStandardNormBall radius x)
        (A.standardNormBallAssignment assignment) :
          BallTerm.Assignment
            (standardRationalBallSystem (E := A.CompletedDirectedPoint))
            (Fin.cons radius context)) := by
  funext i
  exact Fin.cases rfl (fun _ ↦ rfl) i

/-- Every predicate-free typed term commutes with the canonical sort maps. -/
theorem ballToStandardNormBall_realize_term
    (A : XBallTheoryModel.{u}) {n : ℕ} {context : BallContext n}
    {radius : ℚ≥0} (term : BallTerm context radius)
    (assignment : BallTerm.Assignment A.model.toRationalBallSystem context) :
    A.ballToStandardNormBall radius
        (term.realize A.model.toRationalBallSystem assignment) =
      term.realize
        (standardRationalBallSystem (E := A.CompletedDirectedPoint))
        (A.standardNormBallAssignment assignment) := by
  induction term with
  | «variable» i => rfl
  | inclusion h term induction =>
      apply Subtype.ext
      change A.ballToCompletedDirectedPoint _
          (A.model.inclusion h
            (term.realize A.model.toRationalBallSystem assignment)) = _
      rw [A.ballToCompletedDirectedPoint_inclusion h]
      exact congrArg Subtype.val induction
  | zero radius =>
      apply Subtype.ext
      exact A.ballToCompletedDirectedPoint_zero radius
  | neg term induction =>
      apply Subtype.ext
      change A.ballToCompletedDirectedPoint _
          (A.model.neg _
            (term.realize A.model.toRationalBallSystem assignment)) = _
      rw [A.ballToCompletedDirectedPoint_neg]
      exact congrArg Neg.neg (congrArg Subtype.val induction)
  | add left right leftInduction rightInduction =>
      apply Subtype.ext
      change A.ballToCompletedDirectedPoint _
          (A.model.add _ _
            (left.realize A.model.toRationalBallSystem assignment,
              right.realize A.model.toRationalBallSystem assignment)) = _
      rw [A.ballToCompletedDirectedPoint_add]
      exact congrArg₂ (· + ·)
        (congrArg Subtype.val leftInduction)
        (congrArg Subtype.val rightInduction)
  | smul q term induction =>
      apply Subtype.ext
      change A.ballToCompletedDirectedPoint _
          (A.model.smul q _
            (term.realize A.model.toRationalBallSystem assignment)) = _
      rw [A.ballToCompletedDirectedPoint_smul]
      change q • A.ballToCompletedDirectedPoint _
          (term.realize A.model.toRationalBallSystem assignment) =
        (q : ℝ) •
          (term.realize
            (standardRationalBallSystem (E := A.CompletedDirectedPoint))
            (A.standardNormBallAssignment assignment)).1
      rw [Rat.cast_smul_eq_qsmul]
      exact congrArg (q • ·) (congrArg Subtype.val induction)

/-- Predicate-free formula values are preserved by the surjective canonical
maps from the source sorts to the actual closed balls of the completion. -/
theorem realize_predicateFreeReduct_eq_standard
    (A : XBallTheoryModel.{u}) {n : ℕ} {context : BallContext n}
    (formula : BallFormula EmptyBallPredicate emptyBallPredicateRadius context)
    (assignment : BallTerm.Assignment A.model.toRationalBallSystem context) :
    formula.realize A.model.predicateFreeReduct assignment =
      formula.realize (standardBanachBallStructure A.CompletedDirectedPoint)
        (A.standardNormBallAssignment assignment) := by
  induction formula with
  | distance left right =>
      apply Subtype.ext
      change dist (left.realize A.model.toRationalBallSystem assignment)
            (right.realize A.model.toRationalBallSystem assignment) /
          A.model.sortBound _ =
        dist
            (left.realize
              (standardRationalBallSystem (E := A.CompletedDirectedPoint))
              (A.standardNormBallAssignment assignment))
            (right.realize
              (standardRationalBallSystem (E := A.CompletedDirectedPoint))
              (A.standardNormBallAssignment assignment)) /
          rationalBallMetricBound _
      rw [← A.ballToStandardNormBall_realize_term left assignment,
        ← A.ballToStandardNormBall_realize_term right assignment]
      change dist (left.realize A.model.toRationalBallSystem assignment)
            (right.realize A.model.toRationalBallSystem assignment) /
          A.model.sortBound _ =
        dist
            (A.ballToCompletedDirectedPoint _
              (left.realize A.model.toRationalBallSystem assignment))
            (A.ballToCompletedDirectedPoint _
              (right.realize A.model.toRationalBallSystem assignment)) /
          rationalBallMetricBound _
      rw [A.dist_ballToCompletedDirectedPoint]
      field_simp [ne_of_gt (rationalBallMetricBound_pos _)]
  | predicate symbol term => exact nomatch symbol
  | constant value => rfl
  | connective gate children induction =>
      change gate (fun i ↦ (children i).realize A.model.predicateFreeReduct assignment) =
        gate (fun i ↦ (children i).realize
          (standardBanachBallStructure A.CompletedDirectedPoint)
          (A.standardNormBallAssignment assignment))
      congr 1
      funext i
      exact induction i assignment
  | iSup radius formula induction =>
      change (⨆ x : A.model.Ball radius,
          formula.realize A.model.predicateFreeReduct (Fin.cons x assignment)) =
        ⨆ p : RationalNormBall A.CompletedDirectedPoint radius,
          formula.realize (standardBanachBallStructure A.CompletedDirectedPoint)
            (Fin.cons p (A.standardNormBallAssignment assignment))
      apply le_antisymm
      · apply iSup_le
        intro x
        have hx := induction (Fin.cons x assignment)
        rw [A.standardNormBallAssignment_cons] at hx
        exact hx.le.trans <| le_iSup
          (fun p : RationalNormBall A.CompletedDirectedPoint radius ↦
            formula.realize (standardBanachBallStructure A.CompletedDirectedPoint)
              (Fin.cons p (A.standardNormBallAssignment assignment)))
            (A.ballToStandardNormBall radius x)
      · apply iSup_le
        intro p
        obtain ⟨x, rfl⟩ := A.ballToStandardNormBall_surjective radius p
        have hx := induction (Fin.cons x assignment)
        rw [A.standardNormBallAssignment_cons] at hx
        exact hx.ge.trans <| le_iSup (fun x : A.model.Ball radius ↦
          formula.realize A.model.predicateFreeReduct (Fin.cons x assignment)) x
  | iInf radius formula induction =>
      change (⨅ x : A.model.Ball radius,
          formula.realize A.model.predicateFreeReduct (Fin.cons x assignment)) =
        ⨅ p : RationalNormBall A.CompletedDirectedPoint radius,
          formula.realize (standardBanachBallStructure A.CompletedDirectedPoint)
            (Fin.cons p (A.standardNormBallAssignment assignment))
      apply le_antisymm
      · apply le_iInf
        intro p
        obtain ⟨x, rfl⟩ := A.ballToStandardNormBall_surjective radius p
        have hx := induction (Fin.cons x assignment)
        rw [A.standardNormBallAssignment_cons] at hx
        exact (iInf_le (fun x : A.model.Ball radius ↦
          formula.realize A.model.predicateFreeReduct (Fin.cons x assignment)) x).trans hx.le
      · apply le_iInf
        intro x
        have hx := induction (Fin.cons x assignment)
        rw [A.standardNormBallAssignment_cons] at hx
        exact (iInf_le
          (fun p : RationalNormBall A.CompletedDirectedPoint radius ↦
            formula.realize (standardBanachBallStructure A.CompletedDirectedPoint)
              (Fin.cons p (A.standardNormBallAssignment assignment)))
            (A.ballToStandardNormBall radius x)).trans hx.ge

/-- The predicate-free reduct of the typed model and the standard Banach-ball
structure on its reconstructed completion have the same complete theory. -/
theorem predicateFreeReduct_sameCompleteTheory_standard
    (A : XBallTheoryModel.{u}) :
    BallSameCompleteTheory A.model.predicateFreeReduct
      (standardBanachBallStructure A.CompletedDirectedPoint) := by
  intro sentence
  unfold BallSentence.value
  let emptySource : BallTerm.Assignment A.model.toRationalBallSystem
      (Fin.elim0 : BallContext 0) := fun i ↦ nomatch i
  have h := A.realize_predicateFreeReduct_eq_standard sentence
    emptySource
  have hempty : A.standardNormBallAssignment emptySource =
      (fun i : Fin 0 ↦ nomatch i :
        BallTerm.Assignment
          (standardRationalBallSystem (E := A.CompletedDirectedPoint))
          (Fin.elim0 : BallContext 0)) :=
    Subsingleton.elim _ _
  rw [hempty] at h
  simpa only [emptySource] using h

/-- Predicate-free formulas have the same value in the standard X structure
and in the corresponding fragment of the distinguished Hilbert expansion. -/
theorem realize_standardX_eq_expansion_fromPredicateFree
    {n : ℕ} {context : BallContext n}
    (formula : BallFormula EmptyBallPredicate emptyBallPredicateRadius context)
    (assignment : BallTerm.Assignment
      (standardRationalBallSystem (E := NormFormula.X.XSpace)) context) :
    formula.realize (standardBanachBallStructure NormFormula.X.XSpace)
        assignment =
      formula.fromPredicateFree.realize expansionStructure assignment := by
  induction formula with
  | distance left right => rfl
  | predicate symbol term => exact nomatch symbol
  | constant value => rfl
  | connective gate children induction =>
      change gate (fun i ↦ (children i).realize
          (standardBanachBallStructure NormFormula.X.XSpace) assignment) =
        gate (fun i ↦ (children i).fromPredicateFree.realize
          expansionStructure assignment)
      congr 1
      funext i
      exact induction i assignment
  | iSup radius formula induction =>
      change (⨆ x, formula.realize
          (standardBanachBallStructure NormFormula.X.XSpace)
          (Fin.cons x assignment)) =
        ⨆ x, formula.fromPredicateFree.realize expansionStructure
          (Fin.cons x assignment)
      congr 1
      funext x
      exact induction (Fin.cons x assignment)
  | iInf radius formula induction =>
      change (⨅ x, formula.realize
          (standardBanachBallStructure NormFormula.X.XSpace)
          (Fin.cons x assignment)) =
        ⨅ x, formula.fromPredicateFree.realize expansionStructure
          (Fin.cons x assignment)
      congr 1
      funext x
      exact induction (Fin.cons x assignment)

/-- The reconstructed completion itself, with its standard predicate-free
Banach-ball structure, is a model of the predicate-free theory of `X`. -/
theorem standardCompletedDirectedPoint_sameCompleteTheory
    (A : XBallTheoryModel.{u}) :
    BallSameCompleteTheory (standardBanachBallStructure NormFormula.X.XSpace)
      (standardBanachBallStructure A.CompletedDirectedPoint) := by
  have hReduct := A.sameCompleteTheory.predicateFreeReduct
  intro sentence
  calc
    sentence.value (standardBanachBallStructure NormFormula.X.XSpace) =
        BallSentence.value sentence.fromPredicateFree expansionStructure := by
      exact realize_standardX_eq_expansion_fromPredicateFree sentence
        (fun i : Fin 0 ↦ nomatch i)
    _ = sentence.value expansionStructure.predicateFreeReduct := by
      exact BallFormula.realize_fromPredicateFree expansionStructure sentence
        (fun i : Fin 0 ↦ nomatch i)
    _ = sentence.value A.model.predicateFreeReduct := hReduct sentence
    _ = sentence.value
        (standardBanachBallStructure A.CompletedDirectedPoint) :=
      A.predicateFreeReduct_sameCompleteTheory_standard sentence

/-- Typed radius-`2` witnesses retain their radius in the completed Banach space. -/
theorem normAddBallFormula_hasCompletedDistanceAddWitness_two (A : XBallTheoryModel) {low high : ℝ}
    (hIP : normAddBallFormula.HasInfiniteIPWitness A.model low high) :
    A.HasCompletedDistanceAddWitness 2
      (rationalBallMetricBound 4 * low)
      (rationalBallMetricBound 4 * high) := by
  obtain ⟨typedRows, htyped⟩ := hIP
  refine ⟨fun i ↦ A.ballToCompletedDirectedPoint 2 (typedRows i), ?_, ?_⟩
  · intro i
    simpa only [dist_zero_right] using
      A.norm_ballToCompletedDirectedPoint_le_radius 2 (typedRows i)
  · intro E F hdisjoint
    obtain ⟨typedParameter, hlow, hhigh⟩ := htyped E F hdisjoint
    refine ⟨A.ballToCompletedDirectedPoint 2 typedParameter, ?_, ?_, ?_⟩
    · simpa only [dist_zero_right] using
        A.norm_ballToCompletedDirectedPoint_le_radius 2 typedParameter
    · intro i hi
      rw [normAddBallFormula_completedDistance A]
      exact mul_le_mul_of_nonneg_left (hlow i hi)
        (rationalBallMetricBound_pos 4).le
    · intro i hi
      rw [normAddBallFormula_completedDistance A]
      exact mul_le_mul_of_nonneg_left (hhigh i hi)
        (rationalBallMetricBound_pos 4).le


/-- A literal bounded norm-addition witness on the reconstructed carrier is
exactly an infinite witness for the standard typed norm formula. -/
theorem predicateFreeNormAddFormula_hasInfiniteIPWitness_of_completed
    (A : XBallTheoryModel.{u})
    (hWitness : A.HasCompletedNormAddWitness
      4 (Real.sqrt 3) (Real.sqrt 6)) :
    (predicateFreeNormAddFormula 4 4).HasInfiniteIPWitness
      (standardBanachBallStructure A.CompletedDirectedPoint)
      (Real.sqrt 3 / 16) (Real.sqrt 6 / 16) := by
  obtain ⟨rows, hrows, hwitness⟩ := hWitness
  let typedRows : ℕ → RationalNormBall A.CompletedDirectedPoint 4 :=
    fun i ↦ ⟨rows i, hrows i⟩
  refine ⟨typedRows, ?_⟩
  intro E F hdisjoint
  obtain ⟨parameter, hparameter, hlow, hhigh⟩ :=
    hwitness E F hdisjoint
  let typedParameter : RationalNormBall A.CompletedDirectedPoint 4 :=
    ⟨parameter, hparameter⟩
  refine ⟨typedParameter, ?_, ?_⟩
  · intro i hi
    rw [BallFormula.binaryValue, predicateFreeNormAddFormula_value]
    change ‖rows i + parameter‖ / rationalBallMetricBound (4 + 4) ≤
      Real.sqrt 3 / 16
    have hbound : rationalBallMetricBound (4 + 4) = 16 := by
      norm_num [rationalBallMetricBound]
    rw [hbound]
    exact div_le_div_of_nonneg_right (hlow i hi) (by norm_num)
  · intro i hi
    rw [BallFormula.binaryValue, predicateFreeNormAddFormula_value]
    change Real.sqrt 6 / 16 ≤
      ‖rows i + parameter‖ / rationalBallMetricBound (4 + 4)
    have hbound : rationalBallMetricBound (4 + 4) = 16 := by
      norm_num [rationalBallMetricBound]
    rw [hbound]
    exact div_le_div_of_nonneg_right (hhigh i hi) (by norm_num)


/-- The standard radius-`2` norm formula carries the paper's original gap. -/
theorem predicateFreeNormAddFormula_hasInfiniteIPWitness_of_completed_two
    (A : XBallTheoryModel.{u})
    (hWitness : A.HasCompletedNormAddWitness
      2 (Real.sqrt 3) (Real.sqrt 6)) :
    (predicateFreeNormAddFormula 2 2).HasInfiniteIPWitness
      (standardBanachBallStructure A.CompletedDirectedPoint)
      (Real.sqrt 3 / 8) (Real.sqrt 6 / 8) := by
  obtain ⟨rows, hrows, hwitness⟩ := hWitness
  let typedRows : ℕ → RationalNormBall A.CompletedDirectedPoint 2 :=
    fun i ↦ ⟨rows i, hrows i⟩
  refine ⟨typedRows, ?_⟩
  intro E F hdisjoint
  obtain ⟨parameter, hparameter, hlow, hhigh⟩ :=
    hwitness E F hdisjoint
  let typedParameter : RationalNormBall A.CompletedDirectedPoint 2 :=
    ⟨parameter, hparameter⟩
  refine ⟨typedParameter, ?_, ?_⟩
  · intro i hi
    rw [BallFormula.binaryValue, predicateFreeNormAddFormula_value]
    change ‖rows i + parameter‖ / rationalBallMetricBound (2 + 2) ≤
      Real.sqrt 3 / 8
    have hbound : rationalBallMetricBound (2 + 2) = 8 := by
      norm_num [rationalBallMetricBound]
    rw [hbound]
    exact div_le_div_of_nonneg_right (hlow i hi) (by norm_num)
  · intro i hi
    rw [BallFormula.binaryValue, predicateFreeNormAddFormula_value]
    change Real.sqrt 6 / 8 ≤
      ‖rows i + parameter‖ / rationalBallMetricBound (2 + 2)
    have hbound : rationalBallMetricBound (2 + 2) = 8 := by
      norm_num [rationalBallMetricBound]
    rw [hbound]
    exact div_le_div_of_nonneg_right (hhigh i hi) (by norm_num)


end XBallTheoryModel

/-- The public model retains its IP rows and parameters in the paper's `2`-ball. -/
theorem SeparableHilbertianNormAddIPModel.normAddWitness_two
    (M : SeparableHilbertianNormAddIPModel) :
    M.model.HasCompletedNormAddWitness 2 (Real.sqrt 3) (Real.sqrt 6) := by
  apply (M.model.hasCompletedDistanceAddWitness_iff_norm _ _ _).mp
  convert M.model.normAddBallFormula_hasCompletedDistanceAddWitness_two
    M.typedNormAddWitness using 1 <;> norm_num [rationalBallMetricBound] <;> ring

namespace XBallElementaryCopy

variable {A : XBallTheoryModel.{0}} (copy : XBallElementaryCopy A)

/-- The retained copy preserves formulas after forgetting the Hilbert norm
and passing to the actual balls of the reconstructed Banach space. -/
theorem realize_standard
    {n : ℕ} {context : BallContext n}
    (formula : BallFormula EmptyBallPredicate emptyBallPredicateRadius context)
    (assignment : BallTerm.Assignment expansionStructure.toRationalBallSystem context) :
    formula.realize (standardBanachBallStructure A.CompletedDirectedPoint)
        (A.standardNormBallAssignment (fun i ↦ copy.map (context i) (assignment i))) =
      formula.realize (standardBanachBallStructure XSpace) assignment := by
  rw [← A.realize_predicateFreeReduct_eq_standard, ← BallFormula.realize_fromPredicateFree,
    copy.realize_formula, XBallTheoryModel.realize_standardX_eq_expansion_fromPredicateFree]

private theorem point_inclusion {r s : ℚ≥0} (h : r ≤ s) (x : RationalNormBall XSpace r) :
    A.ballToCompletedDirectedPoint s (copy.map s (rationalBallInclusion h x)) =
      A.ballToCompletedDirectedPoint r (copy.map r x) := by
  have ht := copy.realize_term (.inclusion h (unaryVariable r))
    (Fin.cons x (fun i : Fin 0 ↦ nomatch i))
  change A.model.inclusion h (copy.map r x) = copy.map s (rationalBallInclusion h x) at ht
  rw [← ht, A.ballToCompletedDirectedPoint_inclusion]

private def representative (x : XSpace) : Σ r, RationalNormBall XSpace r :=
  ⟨(exists_rationalNormBall x).choose, (exists_rationalNormBall x).choose_spec.choose⟩

private theorem representative_coe (x : XSpace) : ((representative x).2 : XSpace) = x :=
  (exists_rationalNormBall x).choose_spec.choose_spec

private def toPoint (x : XSpace) : A.CompletedDirectedPoint :=
  A.ballToCompletedDirectedPoint (representative x).1
    (copy.map (representative x).1 (representative x).2)

private theorem toPoint_eq (r : ℚ≥0) (x : RationalNormBall XSpace r) :
    copy.toPoint x.1 = A.ballToCompletedDirectedPoint r (copy.map r x) := by
  let y := representative x.1
  have hxy : rationalBallInclusion (le_max_left r y.1) x =
      rationalBallInclusion (le_max_right r y.1) y.2 :=
    Subtype.ext (representative_coe x.1).symm
  change A.ballToCompletedDirectedPoint y.1 (copy.map y.1 y.2) = _
  rw [← copy.point_inclusion (le_max_right r y.1) y.2,
    ← copy.point_inclusion (le_max_left r y.1) x, hxy]

private theorem toPoint_add (x y : XSpace) :
    copy.toPoint (x + y) = copy.toPoint x + copy.toPoint y := by
  obtain ⟨r, x, rfl⟩ := exists_rationalNormBall x
  obtain ⟨s, y, rfl⟩ := exists_rationalNormBall y
  have ht := copy.realize_term (BallTerm.binaryAddTerm r s)
    (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i)))
  change A.model.add r s (copy.map r x, copy.map s y) =
    copy.map (r + s) (rationalBallAdd r s (x, y)) at ht
  change copy.toPoint (rationalBallAdd r s (x, y)).1 = copy.toPoint x.1 + copy.toPoint y.1
  rw [copy.toPoint_eq, copy.toPoint_eq r x, copy.toPoint_eq s y, ← ht,
    A.ballToCompletedDirectedPoint_add]

private theorem toPoint_norm (x : XSpace) : ‖copy.toPoint x‖ = ‖x‖ := by
  obtain ⟨r, x, rfl⟩ := exists_rationalNormBall x
  rw [copy.toPoint_eq r x]
  have h := congrArg (fun t : TruthValue ↦ (t : ℝ)) <|
    copy.realize_standard (.distance (unaryVariable r) (.zero r))
      (Fin.cons x (fun i : Fin 0 ↦ nomatch i))
  change dist (A.ballToCompletedDirectedPoint r (copy.map r x)) 0 /
      rationalBallMetricBound r = dist x.1 0 / rationalBallMetricBound r at h
  simpa only [dist_zero_right] using
    (div_left_inj' (rationalBallMetricBound_pos r).ne').mp h

/-- The sort maps give a single real linear isometry on the whole of `X`. -/
def embedding : XSpace →ₗᵢ[ℝ] A.CompletedDirectedPoint := by
  let f := AddMonoidHom.mk' copy.toPoint copy.toPoint_add
  have h : Isometry f := Isometry.of_dist_eq fun x y ↦ by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub f]
    exact copy.toPoint_norm (x - y)
  exact ⟨(f.toRealLinearMap h.continuous).toLinearMap, copy.toPoint_norm⟩

/-- This linear isometry gives an elementary embedding of the standard
Banach-ball structure of `X` into the reconstructed space. -/
theorem embedding_isElementary : IsElementaryBanachEmbedding copy.embedding := by
  intro n context formula assignment
  have h := copy.realize_standard formula assignment
  have hmaps : (fun i : Fin n ↦
      (⟨copy.embedding (assignment i).1, by
        simpa only [copy.embedding.norm_map] using (assignment i).2⟩ :
        RationalNormBall A.CompletedDirectedPoint (context i))) =
      A.standardNormBallAssignment (fun i ↦ copy.map (context i) (assignment i)) := by
    funext i
    apply Subtype.ext
    exact copy.toPoint_eq (context i) (assignment i)
  rw [← hmaps] at h
  exact h

end XBallElementaryCopy

end

end NormFormula.X.BallLanguage
