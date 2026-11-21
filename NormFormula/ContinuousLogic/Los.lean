import Mathlib.Analysis.SpecificLimits.Basic
import NormFormula.ContinuousLogic.ReducedProduct

/-!
# Łoś's theorem for the bounded reduced product

This file proves that formula evaluation in the metric reduced product is the
ultralimit of coordinate evaluations.  The key quantified step is that taking
an infimum or supremum over all coordinatewise choices commutes with the
ultralimit.  Approximate witnesses with error `1 / (n + 1)` provide the hard
inequalities.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Filter
open scoped Topology

attribute [local instance] Structure.rowPseudoMetricSpace
  Structure.parameterPseudoMetricSpace Structure.rowNonempty
  Structure.parameterNonempty

universe u v

/-- Ultralimits commute with a supremum when the left side ranges over every
sequence of coordinatewise choices. -/
theorem ultralimit_iSup_sequences {α : Type*} [Nonempty α]
    (values : ℕ → α → TruthValue) :
    (⨆ choices : ℕ → α, ultralimit fun n ↦ values n (choices n)) =
      ultralimit (fun n ↦ ⨆ x : α, values n x) := by
  apply le_antisymm
  · refine iSup_le fun choices ↦ ultralimit_mono ?_
    filter_upwards [] with n
    exact le_iSup (values n) (choices n)
  · let error : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
    have herror : Tendsto error indexUltrafilter (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.mono_left indexUltrafilter_le_atTop
    have hexists : ∀ n : ℕ, ∃ x : α,
        ((⨆ a : α, values n a : TruthValue) : ℝ) - error n <
          (values n x : ℝ) := by
      intro n
      have hcoe : ((⨆ a : α, values n a : TruthValue) : ℝ) =
          ⨆ a : α, (values n a : ℝ) :=
        Set.Icc.coe_iSup zero_le_one
      have hlt : ((⨆ a : α, values n a : TruthValue) : ℝ) - error n <
          ⨆ a : α, (values n a : ℝ) := by
        rw [← hcoe]
        exact sub_lt_self _ (by positivity)
      exact exists_lt_of_lt_ciSup hlt
    choose choices hchoices using hexists
    have happrox : ∀ᶠ n in indexUltrafilter,
        ((⨆ x : α, values n x : TruthValue) : ℝ) ≤
          (values n (choices n) : ℝ) + error n := by
      filter_upwards [] with n
      exact (sub_lt_iff_lt_add.mp (hchoices n)).le
    exact (ultralimit_coe_le_of_eventually_le_add_tendsto_zero
      (fun n ↦ ⨆ x : α, values n x)
      (fun n ↦ values n (choices n)) error herror happrox).trans
        (le_iSup (fun choices : ℕ → α ↦
          ultralimit fun n ↦ values n (choices n)) choices)

/-- Ultralimits commute with an infimum when the left side ranges over every
sequence of coordinatewise choices. -/
theorem ultralimit_iInf_sequences {α : Type*} [Nonempty α]
    (values : ℕ → α → TruthValue) :
    (⨅ choices : ℕ → α, ultralimit fun n ↦ values n (choices n)) =
      ultralimit (fun n ↦ ⨅ x : α, values n x) := by
  apply le_antisymm
  · let error : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
    have herror : Tendsto error indexUltrafilter (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.mono_left indexUltrafilter_le_atTop
    have hexists : ∀ n : ℕ, ∃ x : α,
        (values n x : ℝ) <
          ((⨅ a : α, values n a : TruthValue) : ℝ) + error n := by
      intro n
      have hcoe : ((⨅ a : α, values n a : TruthValue) : ℝ) =
          ⨅ a : α, (values n a : ℝ) :=
        Set.Icc.coe_iInf zero_le_one
      have hlt : (⨅ a : α, (values n a : ℝ)) <
          ((⨅ a : α, values n a : TruthValue) : ℝ) + error n := by
        rw [hcoe]
        exact lt_add_of_pos_right _ (by positivity)
      exact exists_lt_of_ciInf_lt hlt
    choose choices hchoices using hexists
    refine (iInf_le (fun choices : ℕ → α ↦
      ultralimit fun n ↦ values n (choices n)) choices).trans ?_
    have happrox : ∀ᶠ n in indexUltrafilter,
        (values n (choices n) : ℝ) ≤
          ((⨅ x : α, values n x : TruthValue) : ℝ) + error n := by
      filter_upwards [] with n
      exact (hchoices n).le
    exact ultralimit_coe_le_of_eventually_le_add_tendsto_zero
      (fun n ↦ values n (choices n))
      (fun n ↦ ⨅ x : α, values n x) error herror happrox
  · refine le_iInf fun choices ↦ ultralimit_mono ?_
    filter_upwards [] with n
    exact iInf_le (values n) (choices n)

namespace Formula

variable (M : Structure.{u, v}) (bounds : M.Bounds)

/-- Łoś's theorem for the minimal bounded language: realizing a formula in
the reduced product at classes of sequence representatives is the ultralimit
of its coordinate realizations. -/
theorem realize_reducedProduct {rowVars parameterVars : ℕ}
    (φ : Formula rowVars parameterVars) :
    ∀ (rows : Fin rowVars → ReducedSequence bounds.row)
      (parameters : Fin parameterVars → ReducedSequence bounds.parameter),
      φ.realize (M.reducedProduct bounds)
          (fun i ↦ ReducedProduct.mk bounds.row (rows i))
          (fun j ↦ ReducedProduct.mk bounds.parameter (parameters j)) =
        ultralimit fun n ↦ φ.realize M
          (fun i ↦ rows i n) (fun j ↦ parameters j n) := by
  induction φ with
  | predicate i j =>
      intro rows parameters
      exact reducedPredicate_mk M bounds (rows i) (parameters j)
  | constant c =>
      intro rows parameters
      exact (ultralimit_const c).symm
  | connective F formulas ih =>
      intro rows parameters
      change F (fun i ↦ (formulas i).realize (M.reducedProduct bounds)
        (fun j ↦ ReducedProduct.mk bounds.row (rows j))
        (fun j ↦ ReducedProduct.mk bounds.parameter (parameters j))) = _
      rw [show (fun i ↦ (formulas i).realize (M.reducedProduct bounds)
          (fun j ↦ ReducedProduct.mk bounds.row (rows j))
          (fun j ↦ ReducedProduct.mk bounds.parameter (parameters j))) =
          (fun i ↦ ultralimit fun n ↦ (formulas i).realize M
            (fun j ↦ rows j n) (fun j ↦ parameters j n)) by
        funext i
        exact ih i rows parameters]
      exact (ultralimit_connective F fun i n ↦ (formulas i).realize M
        (fun j ↦ rows j n) (fun j ↦ parameters j n)).symm
  | iSupRow formula ih =>
      intro rows parameters
      change (⨆ x : ReducedProduct bounds.row,
        formula.realize (M.reducedProduct bounds)
          (Fin.cons x (fun i ↦ ReducedProduct.mk bounds.row (rows i)))
          (fun j ↦ ReducedProduct.mk bounds.parameter (parameters j))) = _
      calc
        _ = ⨆ x : ReducedSequence bounds.row,
            formula.realize (M.reducedProduct bounds)
              (Fin.cons (ReducedProduct.mk bounds.row x)
                (fun i ↦ ReducedProduct.mk bounds.row (rows i)))
              (fun j ↦ ReducedProduct.mk bounds.parameter (parameters j)) :=
          (SeparationQuotient.surjective_mk.iSup_comp _).symm
        _ = ⨆ choices : ReducedSequence bounds.row,
            ultralimit fun n ↦ formula.realize M
              (Fin.cons (choices n) (fun i ↦ rows i n))
              (fun j ↦ parameters j n) := iSup_congr fun x ↦ by
          have h := ih (Fin.cons x rows) parameters
          have hmk := Fin.comp_cons (ReducedProduct.mk bounds.row) x rows
          simp only [Function.comp_def] at hmk
          rw [hmk] at h
          have heval (n : ℕ) :=
            Fin.comp_cons (fun z : ReducedSequence bounds.row ↦ z n) x rows
          simp only [Function.comp_def] at heval
          simpa only [heval] using h
        _ = ultralimit (fun n ↦ ⨆ x : M.Row, formula.realize M
              (Fin.cons x (fun i ↦ rows i n)) (fun j ↦ parameters j n)) :=
          ultralimit_iSup_sequences fun n x ↦ formula.realize M
            (Fin.cons x (fun i ↦ rows i n)) (fun j ↦ parameters j n)
  | iInfRow formula ih =>
      intro rows parameters
      change (⨅ x : ReducedProduct bounds.row,
        formula.realize (M.reducedProduct bounds)
          (Fin.cons x (fun i ↦ ReducedProduct.mk bounds.row (rows i)))
          (fun j ↦ ReducedProduct.mk bounds.parameter (parameters j))) = _
      calc
        _ = ⨅ x : ReducedSequence bounds.row,
            formula.realize (M.reducedProduct bounds)
              (Fin.cons (ReducedProduct.mk bounds.row x)
                (fun i ↦ ReducedProduct.mk bounds.row (rows i)))
              (fun j ↦ ReducedProduct.mk bounds.parameter (parameters j)) :=
          (SeparationQuotient.surjective_mk.iInf_comp _).symm
        _ = ⨅ choices : ReducedSequence bounds.row,
            ultralimit fun n ↦ formula.realize M
              (Fin.cons (choices n) (fun i ↦ rows i n))
              (fun j ↦ parameters j n) := iInf_congr fun x ↦ by
          have h := ih (Fin.cons x rows) parameters
          have hmk := Fin.comp_cons (ReducedProduct.mk bounds.row) x rows
          simp only [Function.comp_def] at hmk
          rw [hmk] at h
          have heval (n : ℕ) :=
            Fin.comp_cons (fun z : ReducedSequence bounds.row ↦ z n) x rows
          simp only [Function.comp_def] at heval
          simpa only [heval] using h
        _ = ultralimit (fun n ↦ ⨅ x : M.Row, formula.realize M
              (Fin.cons x (fun i ↦ rows i n)) (fun j ↦ parameters j n)) :=
          ultralimit_iInf_sequences fun n x ↦ formula.realize M
            (Fin.cons x (fun i ↦ rows i n)) (fun j ↦ parameters j n)
  | iSupParameter formula ih =>
      intro rows parameters
      change (⨆ y : ReducedProduct bounds.parameter,
        formula.realize (M.reducedProduct bounds)
          (fun i ↦ ReducedProduct.mk bounds.row (rows i))
          (Fin.cons y (fun j ↦ ReducedProduct.mk bounds.parameter (parameters j)))) = _
      calc
        _ = ⨆ y : ReducedSequence bounds.parameter,
            formula.realize (M.reducedProduct bounds)
              (fun i ↦ ReducedProduct.mk bounds.row (rows i))
              (Fin.cons (ReducedProduct.mk bounds.parameter y)
                (fun j ↦ ReducedProduct.mk bounds.parameter (parameters j))) :=
          (SeparationQuotient.surjective_mk.iSup_comp _).symm
        _ = ⨆ choices : ReducedSequence bounds.parameter,
            ultralimit fun n ↦ formula.realize M
              (fun i ↦ rows i n)
              (Fin.cons (choices n) (fun j ↦ parameters j n)) := iSup_congr fun y ↦ by
          have h := ih rows (Fin.cons y parameters)
          have hmk := Fin.comp_cons (ReducedProduct.mk bounds.parameter) y parameters
          simp only [Function.comp_def] at hmk
          rw [hmk] at h
          have heval (n : ℕ) :=
            Fin.comp_cons (fun z : ReducedSequence bounds.parameter ↦ z n) y parameters
          simp only [Function.comp_def] at heval
          simpa only [heval] using h
        _ = ultralimit (fun n ↦ ⨆ y : M.Parameter, formula.realize M
              (fun i ↦ rows i n)
              (Fin.cons y (fun j ↦ parameters j n))) :=
          ultralimit_iSup_sequences fun n y ↦ formula.realize M
            (fun i ↦ rows i n) (Fin.cons y (fun j ↦ parameters j n))
  | iInfParameter formula ih =>
      intro rows parameters
      change (⨅ y : ReducedProduct bounds.parameter,
        formula.realize (M.reducedProduct bounds)
          (fun i ↦ ReducedProduct.mk bounds.row (rows i))
          (Fin.cons y (fun j ↦ ReducedProduct.mk bounds.parameter (parameters j)))) = _
      calc
        _ = ⨅ y : ReducedSequence bounds.parameter,
            formula.realize (M.reducedProduct bounds)
              (fun i ↦ ReducedProduct.mk bounds.row (rows i))
              (Fin.cons (ReducedProduct.mk bounds.parameter y)
                (fun j ↦ ReducedProduct.mk bounds.parameter (parameters j))) :=
          (SeparationQuotient.surjective_mk.iInf_comp _).symm
        _ = ⨅ choices : ReducedSequence bounds.parameter,
            ultralimit fun n ↦ formula.realize M
              (fun i ↦ rows i n)
              (Fin.cons (choices n) (fun j ↦ parameters j n)) := iInf_congr fun y ↦ by
          have h := ih rows (Fin.cons y parameters)
          have hmk := Fin.comp_cons (ReducedProduct.mk bounds.parameter) y parameters
          simp only [Function.comp_def] at hmk
          rw [hmk] at h
          have heval (n : ℕ) :=
            Fin.comp_cons (fun z : ReducedSequence bounds.parameter ↦ z n) y parameters
          simp only [Function.comp_def] at heval
          simpa only [heval] using h
        _ = ultralimit (fun n ↦ ⨅ y : M.Parameter, formula.realize M
              (fun i ↦ rows i n)
              (Fin.cons y (fun j ↦ parameters j n))) :=
          ultralimit_iInf_sequences fun n y ↦ formula.realize M
            (fun i ↦ rows i n) (Fin.cons y (fun j ↦ parameters j n))

end Formula

namespace Sentence

variable (M : Structure.{u, v}) (bounds : M.Bounds)

/-- Every sentence has the same value in a bounded structure and its metric
reduced product. -/
@[simp]
theorem value_reducedProduct (φ : Sentence) :
    φ.value (M.reducedProduct bounds) = φ.value M := by
  have h := Formula.realize_reducedProduct M bounds φ
    (fun i : Fin 0 ↦ Fin.elim0 i)
    (fun j : Fin 0 ↦ Fin.elim0 j)
  have hrowProduct :
      (fun i : Fin 0 ↦ ReducedProduct.mk bounds.row
        (Fin.elim0 i : ReducedSequence bounds.row)) =
        (Fin.elim0 : Fin 0 → (M.reducedProduct bounds).Row) :=
    Subsingleton.elim _ _
  have hparameterProduct :
      (fun j : Fin 0 ↦ ReducedProduct.mk bounds.parameter
        (Fin.elim0 j : ReducedSequence bounds.parameter)) =
        (Fin.elim0 : Fin 0 → (M.reducedProduct bounds).Parameter) :=
    Subsingleton.elim _ _
  rw [hrowProduct, hparameterProduct] at h
  have hrowCoordinate (n : ℕ) :
      (fun i : Fin 0 ↦ (Fin.elim0 i : ReducedSequence bounds.row) n) =
        (Fin.elim0 : Fin 0 → M.Row) :=
    Subsingleton.elim _ _
  have hparameterCoordinate (n : ℕ) :
      (fun j : Fin 0 ↦ (Fin.elim0 j : ReducedSequence bounds.parameter) n) =
        (Fin.elim0 : Fin 0 → M.Parameter) :=
    Subsingleton.elim _ _
  simp_rw [hrowCoordinate, hparameterCoordinate] at h
  simpa [Sentence.value] using h

end Sentence

/-- The metric reduced product is a model of the complete theory of the
original bounded structure. -/
theorem sameCompleteTheory_reducedProduct
    (M : Structure.{u, v}) (bounds : M.Bounds) :
    SameCompleteTheory M (M.reducedProduct bounds) := by
  intro φ
  exact (Sentence.value_reducedProduct M bounds φ).symm

end

end NormFormula.ContinuousLogic
