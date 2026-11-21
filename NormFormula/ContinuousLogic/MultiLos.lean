import NormFormula.ContinuousLogic.Los
import NormFormula.ContinuousLogic.MultiReducedProduct

/-!
# Łoś's theorem for a many-predicate reduced product

Formula evaluation in the symbol-indexed metric reduced product is the
ultralimit of its coordinate evaluations.  The quantified cases reuse the
choice-sequence lemmas from the one-predicate proof; only the atomic case now
carries a predicate symbol.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u v w

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.parameterPseudoMetricSpace MultiStructure.rowNonempty
  MultiStructure.parameterNonempty

namespace MultiFormula

variable {Symbol : Type w} (M : MultiStructure.{u, v, w} Symbol)
  (bounds : M.Bounds)

/-- Łoś's theorem for every formula in the many-predicate bounded
language. -/
theorem realize_reducedProduct {rowVars parameterVars : ℕ}
    (φ : MultiFormula Symbol rowVars parameterVars) :
    ∀ (rows : Fin rowVars → ReducedSequence bounds.row)
      (parameters : Fin parameterVars → ReducedSequence bounds.parameter),
      φ.realize (M.reducedProduct bounds)
          (fun i ↦ ReducedProduct.mk bounds.row (rows i))
          (fun j ↦ ReducedProduct.mk bounds.parameter (parameters j)) =
        ultralimit fun n ↦ φ.realize M
          (fun i ↦ rows i n) (fun j ↦ parameters j n) := by
  induction φ with
  | predicate symbol i j =>
      intro rows parameters
      exact multiReducedPredicate_mk M bounds symbol (rows i) (parameters j)
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
              (Fin.cons (choices n) (fun j ↦ parameters j n)) :=
          iSup_congr fun y ↦ by
            have h := ih rows (Fin.cons y parameters)
            have hmk :=
              Fin.comp_cons (ReducedProduct.mk bounds.parameter) y parameters
            simp only [Function.comp_def] at hmk
            rw [hmk] at h
            have heval (n : ℕ) := Fin.comp_cons
              (fun z : ReducedSequence bounds.parameter ↦ z n) y parameters
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
              (Fin.cons (choices n) (fun j ↦ parameters j n)) :=
          iInf_congr fun y ↦ by
            have h := ih rows (Fin.cons y parameters)
            have hmk :=
              Fin.comp_cons (ReducedProduct.mk bounds.parameter) y parameters
            simp only [Function.comp_def] at hmk
            rw [hmk] at h
            have heval (n : ℕ) := Fin.comp_cons
              (fun z : ReducedSequence bounds.parameter ↦ z n) y parameters
            simp only [Function.comp_def] at heval
            simpa only [heval] using h
        _ = ultralimit (fun n ↦ ⨅ y : M.Parameter, formula.realize M
              (fun i ↦ rows i n)
              (Fin.cons y (fun j ↦ parameters j n))) :=
          ultralimit_iInf_sequences fun n y ↦ formula.realize M
            (fun i ↦ rows i n) (Fin.cons y (fun j ↦ parameters j n))

end MultiFormula

namespace MultiSentence

variable {Symbol : Type w} (M : MultiStructure.{u, v, w} Symbol)
  (bounds : M.Bounds)

/-- Every sentence has the same value in a bounded many-predicate structure
and its metric reduced product. -/
@[simp]
theorem value_reducedProduct (φ : MultiSentence Symbol) :
    φ.value (M.reducedProduct bounds) = φ.value M := by
  have h := MultiFormula.realize_reducedProduct M bounds φ
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
  simpa [MultiSentence.value] using h

end MultiSentence

/-- The many-predicate metric reduced product is a model of the complete
theory of the original bounded structure. -/
theorem multiSameCompleteTheory_reducedProduct
    {Symbol : Type w} (M : MultiStructure.{u, v, w} Symbol)
    (bounds : M.Bounds) :
    MultiSameCompleteTheory M (M.reducedProduct bounds) := by
  intro φ
  exact (MultiSentence.value_reducedProduct M bounds φ).symm

end

end NormFormula.ContinuousLogic
