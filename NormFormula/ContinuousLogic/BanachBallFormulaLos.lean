import NormFormula.ContinuousLogic.BanachBallFormulaContinuity
import NormFormula.ContinuousLogic.BanachBallFormulaLosBasic
import NormFormula.ContinuousLogic.Los

/-!
# Łoś's theorem for completed rational-ball reduced products

The completed reduced balls contain the metric quotients only densely, so the
quantified cases require one extra step beyond the earlier bounded-language
proof.  A continuous truth-valued function has the same supremum and infimum
on a completion as on the canonical dense image.  After this reduction,
surjectivity of the separation quotient and the existing
ultralimit-of-choice-sequences identities give the supremum and infimum Łoś
steps.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open UniformSpace
open scoped Topology

universe u w

/-- A continuous truth-valued function has the same supremum on a completion
as on the canonical dense image. -/
theorem iSup_completion_eq {A : Type u} [PseudoMetricSpace A]
    (f : Completion A → TruthValue) (hf : Continuous f) :
    (⨆ x : Completion A, f x) = ⨆ x : A, f x := by
  apply le_antisymm
  · refine iSup_le fun x ↦ ?_
    induction x using Completion.induction_on with
    | hp => exact isClosed_le hf continuous_const
    | ih x => exact le_iSup (fun y : A ↦ f y) x
  · exact iSup_comp_le f ((↑) : A → Completion A)

/-- A continuous truth-valued function has the same infimum on a completion
as on the canonical dense image. -/
theorem iInf_completion_eq {A : Type u} [PseudoMetricSpace A]
    (f : Completion A → TruthValue) (hf : Continuous f) :
    (⨅ x : Completion A, f x) = ⨅ x : A, f x := by
  apply le_antisymm
  · exact le_iInf fun x ↦ iInf_le (fun y : Completion A ↦ f y) x
  · refine le_iInf fun x ↦ ?_
    induction x using Completion.induction_on with
    | hp => exact isClosed_le continuous_const hf
    | ih x => exact iInf_le (fun y : A ↦ f y) x

namespace BallFormula

variable {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
variable (M : BallStructure.{u, w} Symbol symbolRadius)

/-- Varying only the newly bound variable gives a uniformly continuous map
into the dependent assignment space. -/
theorem uniformContinuous_cons_assignment
    {n : ℕ} {context : BallContext n} (r : ℚ≥0)
    (assignment : BallTerm.Assignment M.toRationalBallSystem context) :
    UniformContinuous
      (fun x : M.Ball r ↦
        (Fin.cons x assignment : BallTerm.Assignment M.toRationalBallSystem
          (Fin.cons r context))) := by
  apply uniformContinuous_pi.mpr
  intro i
  refine Fin.cases ?_ (fun _ ↦ ?_) i
  · exact uniformContinuous_id
  · exact uniformContinuous_const

/-- The supremum quantifier preserves the typed reduced-product Łoś
property. -/
theorem hasReducedProductLos_iSup
    {n : ℕ} {context : BallContext n} (r : ℚ≥0)
    (formula : BallFormula Symbol symbolRadius (Fin.cons r context))
    (hformula : HasReducedProductLos M formula) :
    HasReducedProductLos M (.iSup r formula) := by
  intro assignment
  let S := M.toRationalBallSystem
  let B := S.reducedBound r
  let completed : BallTerm.Assignment S.reducedProduct context :=
    BallTerm.completedAssignment S assignment
  have hcontinuous : Continuous
      (fun x : Completion (ReducedProduct B) ↦
        formula.realize M.reducedProduct (Fin.cons x completed)) :=
    (formula.realize_continuous M.reducedProduct).comp
      (uniformContinuous_cons_assignment M.reducedProduct r completed).continuous
  change (⨆ x : Completion (ReducedProduct B),
      formula.realize M.reducedProduct (Fin.cons x completed)) = _
  calc
    _ = ⨆ x : ReducedProduct B,
        formula.realize M.reducedProduct (Fin.cons (x : Completion (ReducedProduct B)) completed) :=
      iSup_completion_eq _ hcontinuous
    _ = ⨆ x : ReducedSequence B,
        formula.realize M.reducedProduct
          (Fin.cons (ReducedProduct.completedMk B x) completed) :=
      (SeparationQuotient.surjective_mk.iSup_comp _).symm
    _ = ⨆ choices : ReducedSequence B,
        ultralimit fun k ↦ formula.realize M
          (Fin.cons (choices k) (BallTerm.coordinateAssignment S assignment k)) :=
      iSup_congr fun choices ↦ by
        have h := hformula (Fin.cons choices assignment)
        have hcompleted : BallTerm.completedAssignment S (Fin.cons choices assignment) =
            (show BallTerm.Assignment S.reducedProduct (Fin.cons r context) from
              Fin.cons (ReducedProduct.completedMk B choices) completed) := by
          funext i
          refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
        have hcoordinate (k : ℕ) :
            BallTerm.coordinateAssignment S (Fin.cons choices assignment) k =
              (show BallTerm.Assignment S (Fin.cons r context) from
                Fin.cons (choices k) (BallTerm.coordinateAssignment S assignment k)) := by
          funext i
          refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
        change formula.realize M.reducedProduct
            (BallTerm.completedAssignment S (Fin.cons choices assignment)) =
          ultralimit (fun k ↦ formula.realize M
            (BallTerm.coordinateAssignment S (Fin.cons choices assignment) k)) at h
        rw [hcompleted] at h
        have hvalues :
            (fun k ↦ formula.realize M
              (BallTerm.coordinateAssignment S (Fin.cons choices assignment) k)) =
            (fun k ↦ formula.realize M
              (Fin.cons (choices k) (BallTerm.coordinateAssignment S assignment k))) := by
          funext k
          rw [hcoordinate k]
        rw [hvalues] at h
        exact h
    _ = ultralimit (fun k ↦ ⨆ x : M.Ball r,
        formula.realize M
          (Fin.cons x (BallTerm.coordinateAssignment S assignment k))) :=
      ultralimit_iSup_sequences fun k x ↦ formula.realize M
        (Fin.cons x (BallTerm.coordinateAssignment S assignment k))

/-- The infimum quantifier preserves the typed reduced-product Łoś
property. -/
theorem hasReducedProductLos_iInf
    {n : ℕ} {context : BallContext n} (r : ℚ≥0)
    (formula : BallFormula Symbol symbolRadius (Fin.cons r context))
    (hformula : HasReducedProductLos M formula) :
    HasReducedProductLos M (.iInf r formula) := by
  intro assignment
  let S := M.toRationalBallSystem
  let B := S.reducedBound r
  let completed : BallTerm.Assignment S.reducedProduct context :=
    BallTerm.completedAssignment S assignment
  have hcontinuous : Continuous
      (fun x : Completion (ReducedProduct B) ↦
        formula.realize M.reducedProduct (Fin.cons x completed)) :=
    (formula.realize_continuous M.reducedProduct).comp
      (uniformContinuous_cons_assignment M.reducedProduct r completed).continuous
  change (⨅ x : Completion (ReducedProduct B),
      formula.realize M.reducedProduct (Fin.cons x completed)) = _
  calc
    _ = ⨅ x : ReducedProduct B,
        formula.realize M.reducedProduct (Fin.cons (x : Completion (ReducedProduct B)) completed) :=
      iInf_completion_eq _ hcontinuous
    _ = ⨅ x : ReducedSequence B,
        formula.realize M.reducedProduct
          (Fin.cons (ReducedProduct.completedMk B x) completed) :=
      (SeparationQuotient.surjective_mk.iInf_comp _).symm
    _ = ⨅ choices : ReducedSequence B,
        ultralimit fun k ↦ formula.realize M
          (Fin.cons (choices k) (BallTerm.coordinateAssignment S assignment k)) :=
      iInf_congr fun choices ↦ by
        have h := hformula (Fin.cons choices assignment)
        have hcompleted : BallTerm.completedAssignment S (Fin.cons choices assignment) =
            (show BallTerm.Assignment S.reducedProduct (Fin.cons r context) from
              Fin.cons (ReducedProduct.completedMk B choices) completed) := by
          funext i
          refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
        have hcoordinate (k : ℕ) :
            BallTerm.coordinateAssignment S (Fin.cons choices assignment) k =
              (show BallTerm.Assignment S (Fin.cons r context) from
                Fin.cons (choices k) (BallTerm.coordinateAssignment S assignment k)) := by
          funext i
          refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
        change formula.realize M.reducedProduct
            (BallTerm.completedAssignment S (Fin.cons choices assignment)) =
          ultralimit (fun k ↦ formula.realize M
            (BallTerm.coordinateAssignment S (Fin.cons choices assignment) k)) at h
        rw [hcompleted] at h
        have hvalues :
            (fun k ↦ formula.realize M
              (BallTerm.coordinateAssignment S (Fin.cons choices assignment) k)) =
            (fun k ↦ formula.realize M
              (Fin.cons (choices k) (BallTerm.coordinateAssignment S assignment k))) := by
          funext k
          rw [hcoordinate k]
        rw [hvalues] at h
        exact h
    _ = ultralimit (fun k ↦ ⨅ x : M.Ball r,
        formula.realize M
          (Fin.cons x (BallTerm.coordinateAssignment S assignment k))) :=
      ultralimit_iInf_sequences fun k x ↦ formula.realize M
        (Fin.cons x (BallTerm.coordinateAssignment S assignment k))

/-- Full Łoś theorem for every typed rational-ball formula. -/
theorem hasReducedProductLos
    {n : ℕ} {context : BallContext n}
    (formula : BallFormula Symbol symbolRadius context) :
    HasReducedProductLos M formula := by
  induction formula with
  | distance left right => exact hasReducedProductLos_distance M left right
  | predicate symbol term => exact hasReducedProductLos_predicate M symbol term
  | constant value => exact hasReducedProductLos_constant M value
  | connective gate children induction =>
      exact hasReducedProductLos_connective M gate children induction
  | iSup r formula induction => exact hasReducedProductLos_iSup M r formula induction
  | iInf r formula induction => exact hasReducedProductLos_iInf M r formula induction

/-- Pointwise full typed formula Łoś theorem. -/
@[simp]
theorem realize_reducedProduct
    {n : ℕ} {context : BallContext n}
    (formula : BallFormula Symbol symbolRadius context)
    (assignment : BallTerm.ReducedAssignment M.toRationalBallSystem context) :
    formula.realize M.reducedProduct
        (BallTerm.completedAssignment M.toRationalBallSystem assignment) =
      ultralimit fun k ↦ formula.realize M
        (BallTerm.coordinateAssignment M.toRationalBallSystem assignment k) :=
  hasReducedProductLos M formula assignment

end BallFormula

namespace BallSentence

variable {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
variable (M : BallStructure.{u, w} Symbol symbolRadius)

/-- Every sentence has the same value in a ball structure and its completed
reduced product. -/
@[simp]
theorem value_reducedProduct (sentence : BallSentence Symbol symbolRadius) :
    sentence.value M.reducedProduct = sentence.value M := by
  have h := BallFormula.realize_reducedProduct M sentence
    (fun i : Fin 0 ↦ Fin.elim0 i)
  have hproduct : BallTerm.completedAssignment M.toRationalBallSystem
      (fun i : Fin 0 ↦ (Fin.elim0 i :
        ReducedSequence (M.toRationalBallSystem.reducedBound
          ((Fin.elim0 : BallContext 0) i)))) =
      (fun i : Fin 0 ↦ Fin.elim0 i) :=
    Subsingleton.elim _ _
  rw [hproduct] at h
  have hcoordinate (k : ℕ) : BallTerm.coordinateAssignment M.toRationalBallSystem
      (fun i : Fin 0 ↦ (Fin.elim0 i :
        ReducedSequence (M.toRationalBallSystem.reducedBound
          ((Fin.elim0 : BallContext 0) i)))) k =
      (fun i : Fin 0 ↦ Fin.elim0 i) :=
    Subsingleton.elim _ _
  simp_rw [hcoordinate] at h
  unfold BallSentence.value
  have hproductFinal :
      ((fun i : Fin 0 ↦ Fin.elim0 i) :
        BallTerm.Assignment M.reducedProduct.toRationalBallSystem
          (Fin.elim0 : BallContext 0)) =
      (fun i : Fin 0 ↦ nomatch i) :=
    Subsingleton.elim _ _
  have hcoordinateFinal :
      ((fun i : Fin 0 ↦ Fin.elim0 i) :
        BallTerm.Assignment M.toRationalBallSystem (Fin.elim0 : BallContext 0)) =
      (fun i : Fin 0 ↦ nomatch i) :=
    Subsingleton.elim _ _
  rw [ultralimit_const] at h
  calc
    _ = sentence.realize M.reducedProduct (fun i : Fin 0 ↦ Fin.elim0 i) :=
      congrArg (sentence.realize M.reducedProduct) hproductFinal.symm
    _ = sentence.realize M (fun i : Fin 0 ↦ Fin.elim0 i) := h
    _ = _ := congrArg (sentence.realize M) hcoordinateFinal

end BallSentence

/-- The completed rational-ball reduced product is a model of the same full
typed complete theory. -/
theorem ballSameCompleteTheory_reducedProduct
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius) :
    BallSameCompleteTheory M M.reducedProduct := by
  intro sentence
  exact (BallSentence.value_reducedProduct M sentence).symm

end


end NormFormula.ContinuousLogic
