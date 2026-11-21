import NormFormula.ContinuousLogic.ReducedProductAlong

/-!
# Łoś's theorem along an arbitrary ultrafilter

Quantifier witnesses are selected independently at every index.  An explicit
positive error scale tending to zero supplies the approximate witnesses for
infima and suprema.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Filter
open scoped Topology

universe κ u v w l

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.parameterPseudoMetricSpace MultiStructure.rowNonempty
  MultiStructure.parameterNonempty

/-- Positive coordinate errors tending to zero along an ultrafilter. -/
structure UltrafilterApproximationScale {ι : Type κ} (U : Ultrafilter ι) where
  error : ι → ℝ
  error_pos : ∀ i, 0 < error i
  tendsto_zero : Tendsto error U (𝓝 0)

/-- Arbitrary-index ultralimits commute with a supremum over all
coordinatewise choices. -/
theorem ultralimitAlong_iSup_families {ι : Type κ} {α : Type l}
    [Nonempty α] (U : Ultrafilter ι) (scale : UltrafilterApproximationScale U)
    (values : ι → α → TruthValue) :
    (⨆ choices : ι → α, ultralimitAlong U fun i ↦ values i (choices i)) =
      ultralimitAlong U (fun i ↦ ⨆ x : α, values i x) := by
  apply le_antisymm
  · refine iSup_le fun choices ↦ ultralimitAlong_mono ?_
    filter_upwards [] with i
    exact le_iSup (values i) (choices i)
  · have hexists : ∀ i : ι, ∃ x : α,
        ((⨆ a : α, values i a : TruthValue) : ℝ) - scale.error i <
          (values i x : ℝ) := by
      intro i
      have hcoe : ((⨆ a : α, values i a : TruthValue) : ℝ) =
          ⨆ a : α, (values i a : ℝ) :=
        Set.Icc.coe_iSup zero_le_one
      have hlt : ((⨆ a : α, values i a : TruthValue) : ℝ) -
          scale.error i < ⨆ a : α, (values i a : ℝ) := by
        rw [← hcoe]
        exact sub_lt_self _ (scale.error_pos i)
      exact exists_lt_of_lt_ciSup hlt
    choose choices hchoices using hexists
    have happrox : ∀ᶠ i in U,
        ((⨆ x : α, values i x : TruthValue) : ℝ) ≤
          (values i (choices i) : ℝ) + scale.error i := by
      filter_upwards [] with i
      exact (sub_lt_iff_lt_add.mp (hchoices i)).le
    exact (ultralimitAlong_coe_le_of_eventually_le_add_tendsto_zero
      U (fun i ↦ ⨆ x : α, values i x)
      (fun i ↦ values i (choices i)) scale.error scale.tendsto_zero happrox).trans
        (le_iSup (fun choices : ι → α ↦
          ultralimitAlong U fun i ↦ values i (choices i)) choices)

/-- Arbitrary-index ultralimits commute with an infimum over all
coordinatewise choices. -/
theorem ultralimitAlong_iInf_families {ι : Type κ} {α : Type l}
    [Nonempty α] (U : Ultrafilter ι) (scale : UltrafilterApproximationScale U)
    (values : ι → α → TruthValue) :
    (⨅ choices : ι → α, ultralimitAlong U fun i ↦ values i (choices i)) =
      ultralimitAlong U (fun i ↦ ⨅ x : α, values i x) := by
  apply le_antisymm
  · have hexists : ∀ i : ι, ∃ x : α,
        (values i x : ℝ) <
          ((⨅ a : α, values i a : TruthValue) : ℝ) + scale.error i := by
      intro i
      have hcoe : ((⨅ a : α, values i a : TruthValue) : ℝ) =
          ⨅ a : α, (values i a : ℝ) :=
        Set.Icc.coe_iInf zero_le_one
      have hlt : (⨅ a : α, (values i a : ℝ)) <
          ((⨅ a : α, values i a : TruthValue) : ℝ) + scale.error i := by
        rw [hcoe]
        exact lt_add_of_pos_right _ (scale.error_pos i)
      exact exists_lt_of_ciInf_lt hlt
    choose choices hchoices using hexists
    refine (iInf_le (fun choices : ι → α ↦
      ultralimitAlong U fun i ↦ values i (choices i)) choices).trans ?_
    have happrox : ∀ᶠ i in U,
        (values i (choices i) : ℝ) ≤
          ((⨅ x : α, values i x : TruthValue) : ℝ) + scale.error i := by
      filter_upwards [] with i
      exact (hchoices i).le
    exact ultralimitAlong_coe_le_of_eventually_le_add_tendsto_zero
      U (fun i ↦ values i (choices i))
      (fun i ↦ ⨅ x : α, values i x) scale.error scale.tendsto_zero happrox
  · refine le_iInf fun choices ↦ ultralimitAlong_mono ?_
    filter_upwards [] with i
    exact iInf_le (values i) (choices i)

namespace MultiFormula

variable {ι : Type κ} (U : Ultrafilter ι)
  (scale : UltrafilterApproximationScale U)
  {Symbol : Type w} (M : MultiStructure.{u, v, w} Symbol)
  (bounds : M.Bounds)

include scale

/-- Łoś's theorem for every many-predicate formula along `U`. -/
theorem realize_reducedProductAlong {rowVars parameterVars : ℕ}
    (φ : MultiFormula Symbol rowVars parameterVars) :
    ∀ (rows : Fin rowVars → ReducedSequenceAlong U bounds.row)
      (parameters : Fin parameterVars →
        ReducedSequenceAlong U bounds.parameter),
      φ.realize (M.reducedProductAlong U bounds)
          (fun i ↦ ReducedProductAlong.mk U bounds.row (rows i))
          (fun j ↦ ReducedProductAlong.mk U bounds.parameter (parameters j)) =
        ultralimitAlong U fun k ↦ φ.realize M
          (fun i ↦ rows i k) (fun j ↦ parameters j k) := by
  induction φ with
  | predicate symbol i j =>
      intro rows parameters
      exact multiReducedPredicateAlong_mk U M bounds symbol
        (rows i) (parameters j)
  | constant c =>
      intro rows parameters
      exact (ultralimitAlong_const U c).symm
  | connective F formulas ih =>
      intro rows parameters
      change F (fun i ↦ (formulas i).realize (M.reducedProductAlong U bounds)
        (fun j ↦ ReducedProductAlong.mk U bounds.row (rows j))
        (fun j ↦ ReducedProductAlong.mk U bounds.parameter (parameters j))) = _
      rw [show (fun i ↦ (formulas i).realize (M.reducedProductAlong U bounds)
          (fun j ↦ ReducedProductAlong.mk U bounds.row (rows j))
          (fun j ↦ ReducedProductAlong.mk U bounds.parameter (parameters j))) =
          (fun i ↦ ultralimitAlong U fun k ↦ (formulas i).realize M
            (fun j ↦ rows j k) (fun j ↦ parameters j k)) by
        funext i
        exact ih i rows parameters]
      exact (ultralimitAlong_connective U F fun i k ↦
        (formulas i).realize M
          (fun j ↦ rows j k) (fun j ↦ parameters j k)).symm
  | iSupRow formula ih =>
      intro rows parameters
      change (⨆ x : ReducedProductAlong U bounds.row,
        formula.realize (M.reducedProductAlong U bounds)
          (Fin.cons x (fun i ↦ ReducedProductAlong.mk U bounds.row (rows i)))
          (fun j ↦ ReducedProductAlong.mk U bounds.parameter (parameters j))) = _
      calc
        _ = ⨆ x : ReducedSequenceAlong U bounds.row,
            formula.realize (M.reducedProductAlong U bounds)
              (Fin.cons (ReducedProductAlong.mk U bounds.row x)
                (fun i ↦ ReducedProductAlong.mk U bounds.row (rows i)))
              (fun j ↦ ReducedProductAlong.mk U bounds.parameter (parameters j)) :=
          (SeparationQuotient.surjective_mk.iSup_comp _).symm
        _ = ⨆ choices : ReducedSequenceAlong U bounds.row,
            ultralimitAlong U fun k ↦ formula.realize M
              (Fin.cons (choices k) (fun i ↦ rows i k))
              (fun j ↦ parameters j k) := iSup_congr fun x ↦ by
          have h := ih (Fin.cons x rows) parameters
          have hmk := Fin.comp_cons (ReducedProductAlong.mk U bounds.row) x rows
          simp only [Function.comp_def] at hmk
          rw [hmk] at h
          have heval (k : ι) :=
            Fin.comp_cons (fun z : ReducedSequenceAlong U bounds.row ↦ z k) x rows
          simp only [Function.comp_def] at heval
          simpa only [heval] using h
        _ = ultralimitAlong U (fun k ↦ ⨆ x : M.Row, formula.realize M
              (Fin.cons x (fun i ↦ rows i k))
              (fun j ↦ parameters j k)) :=
          ultralimitAlong_iSup_families U scale fun k x ↦ formula.realize M
            (Fin.cons x (fun i ↦ rows i k)) (fun j ↦ parameters j k)
  | iInfRow formula ih =>
      intro rows parameters
      change (⨅ x : ReducedProductAlong U bounds.row,
        formula.realize (M.reducedProductAlong U bounds)
          (Fin.cons x (fun i ↦ ReducedProductAlong.mk U bounds.row (rows i)))
          (fun j ↦ ReducedProductAlong.mk U bounds.parameter (parameters j))) = _
      calc
        _ = ⨅ x : ReducedSequenceAlong U bounds.row,
            formula.realize (M.reducedProductAlong U bounds)
              (Fin.cons (ReducedProductAlong.mk U bounds.row x)
                (fun i ↦ ReducedProductAlong.mk U bounds.row (rows i)))
              (fun j ↦ ReducedProductAlong.mk U bounds.parameter (parameters j)) :=
          (SeparationQuotient.surjective_mk.iInf_comp _).symm
        _ = ⨅ choices : ReducedSequenceAlong U bounds.row,
            ultralimitAlong U fun k ↦ formula.realize M
              (Fin.cons (choices k) (fun i ↦ rows i k))
              (fun j ↦ parameters j k) := iInf_congr fun x ↦ by
          have h := ih (Fin.cons x rows) parameters
          have hmk := Fin.comp_cons (ReducedProductAlong.mk U bounds.row) x rows
          simp only [Function.comp_def] at hmk
          rw [hmk] at h
          have heval (k : ι) :=
            Fin.comp_cons (fun z : ReducedSequenceAlong U bounds.row ↦ z k) x rows
          simp only [Function.comp_def] at heval
          simpa only [heval] using h
        _ = ultralimitAlong U (fun k ↦ ⨅ x : M.Row, formula.realize M
              (Fin.cons x (fun i ↦ rows i k))
              (fun j ↦ parameters j k)) :=
          ultralimitAlong_iInf_families U scale fun k x ↦ formula.realize M
            (Fin.cons x (fun i ↦ rows i k)) (fun j ↦ parameters j k)
  | iSupParameter formula ih =>
      intro rows parameters
      change (⨆ y : ReducedProductAlong U bounds.parameter,
        formula.realize (M.reducedProductAlong U bounds)
          (fun i ↦ ReducedProductAlong.mk U bounds.row (rows i))
          (Fin.cons y
            (fun j ↦ ReducedProductAlong.mk U bounds.parameter (parameters j)))) = _
      calc
        _ = ⨆ y : ReducedSequenceAlong U bounds.parameter,
            formula.realize (M.reducedProductAlong U bounds)
              (fun i ↦ ReducedProductAlong.mk U bounds.row (rows i))
              (Fin.cons (ReducedProductAlong.mk U bounds.parameter y)
                (fun j ↦ ReducedProductAlong.mk U bounds.parameter (parameters j))) :=
          (SeparationQuotient.surjective_mk.iSup_comp _).symm
        _ = ⨆ choices : ReducedSequenceAlong U bounds.parameter,
            ultralimitAlong U fun k ↦ formula.realize M
              (fun i ↦ rows i k)
              (Fin.cons (choices k) (fun j ↦ parameters j k)) :=
          iSup_congr fun y ↦ by
            have h := ih rows (Fin.cons y parameters)
            have hmk :=
              Fin.comp_cons (ReducedProductAlong.mk U bounds.parameter) y parameters
            simp only [Function.comp_def] at hmk
            rw [hmk] at h
            have heval (k : ι) := Fin.comp_cons
              (fun z : ReducedSequenceAlong U bounds.parameter ↦ z k) y parameters
            simp only [Function.comp_def] at heval
            simpa only [heval] using h
        _ = ultralimitAlong U (fun k ↦ ⨆ y : M.Parameter, formula.realize M
              (fun i ↦ rows i k)
              (Fin.cons y (fun j ↦ parameters j k))) :=
          ultralimitAlong_iSup_families U scale fun k y ↦ formula.realize M
            (fun i ↦ rows i k) (Fin.cons y (fun j ↦ parameters j k))
  | iInfParameter formula ih =>
      intro rows parameters
      change (⨅ y : ReducedProductAlong U bounds.parameter,
        formula.realize (M.reducedProductAlong U bounds)
          (fun i ↦ ReducedProductAlong.mk U bounds.row (rows i))
          (Fin.cons y
            (fun j ↦ ReducedProductAlong.mk U bounds.parameter (parameters j)))) = _
      calc
        _ = ⨅ y : ReducedSequenceAlong U bounds.parameter,
            formula.realize (M.reducedProductAlong U bounds)
              (fun i ↦ ReducedProductAlong.mk U bounds.row (rows i))
              (Fin.cons (ReducedProductAlong.mk U bounds.parameter y)
                (fun j ↦ ReducedProductAlong.mk U bounds.parameter (parameters j))) :=
          (SeparationQuotient.surjective_mk.iInf_comp _).symm
        _ = ⨅ choices : ReducedSequenceAlong U bounds.parameter,
            ultralimitAlong U fun k ↦ formula.realize M
              (fun i ↦ rows i k)
              (Fin.cons (choices k) (fun j ↦ parameters j k)) :=
          iInf_congr fun y ↦ by
            have h := ih rows (Fin.cons y parameters)
            have hmk :=
              Fin.comp_cons (ReducedProductAlong.mk U bounds.parameter) y parameters
            simp only [Function.comp_def] at hmk
            rw [hmk] at h
            have heval (k : ι) := Fin.comp_cons
              (fun z : ReducedSequenceAlong U bounds.parameter ↦ z k) y parameters
            simp only [Function.comp_def] at heval
            simpa only [heval] using h
        _ = ultralimitAlong U (fun k ↦ ⨅ y : M.Parameter, formula.realize M
              (fun i ↦ rows i k)
              (Fin.cons y (fun j ↦ parameters j k))) :=
          ultralimitAlong_iInf_families U scale fun k y ↦ formula.realize M
            (fun i ↦ rows i k) (Fin.cons y (fun j ↦ parameters j k))

end MultiFormula

namespace MultiSentence

variable {ι : Type κ} (U : Ultrafilter ι)
  (scale : UltrafilterApproximationScale U)
  {Symbol : Type w} (M : MultiStructure.{u, v, w} Symbol)
  (bounds : M.Bounds)

include scale

/-- Sentence values are preserved by the arbitrary-index reduced product. -/
@[simp]
theorem value_reducedProductAlong (φ : MultiSentence Symbol) :
    φ.value (M.reducedProductAlong U bounds) = φ.value M := by
  have h := MultiFormula.realize_reducedProductAlong U scale M bounds φ
    (fun i : Fin 0 ↦ Fin.elim0 i) (fun j : Fin 0 ↦ Fin.elim0 j)
  have hrowProduct :
      (fun i : Fin 0 ↦ ReducedProductAlong.mk U bounds.row
        (Fin.elim0 i : ReducedSequenceAlong U bounds.row)) =
        (Fin.elim0 : Fin 0 → (M.reducedProductAlong U bounds).Row) :=
    Subsingleton.elim _ _
  have hparameterProduct :
      (fun j : Fin 0 ↦ ReducedProductAlong.mk U bounds.parameter
        (Fin.elim0 j : ReducedSequenceAlong U bounds.parameter)) =
        (Fin.elim0 : Fin 0 → (M.reducedProductAlong U bounds).Parameter) :=
    Subsingleton.elim _ _
  rw [hrowProduct, hparameterProduct] at h
  have hrowCoordinate (k : ι) :
      (fun i : Fin 0 ↦ (Fin.elim0 i : ReducedSequenceAlong U bounds.row) k) =
        (Fin.elim0 : Fin 0 → M.Row) :=
    Subsingleton.elim _ _
  have hparameterCoordinate (k : ι) :
      (fun j : Fin 0 ↦
        (Fin.elim0 j : ReducedSequenceAlong U bounds.parameter) k) =
        (Fin.elim0 : Fin 0 → M.Parameter) :=
    Subsingleton.elim _ _
  simp_rw [hrowCoordinate, hparameterCoordinate] at h
  simpa [MultiSentence.value] using h

end MultiSentence

/-- The arbitrary-index reduced product has the same complete theory. -/
theorem multiSameCompleteTheory_reducedProductAlong
    {ι : Type κ} (U : Ultrafilter ι)
    (scale : UltrafilterApproximationScale U)
    {Symbol : Type w} (M : MultiStructure.{u, v, w} Symbol)
    (bounds : M.Bounds) :
    MultiSameCompleteTheory M (M.reducedProductAlong U bounds) := by
  intro φ
  exact (MultiSentence.value_reducedProductAlong U scale M bounds φ).symm

end

end NormFormula.ContinuousLogic
