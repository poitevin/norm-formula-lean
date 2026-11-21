import NormFormula.ContinuousLogic.WitnessLimitClosure

/-!
# Uniform continuity of formula evaluation

Evaluation of every unrestricted `MultiFormula` is uniformly continuous in
its finite tuple of free row and parameter assignments.  The quantifier cases
use the same child modulus for every value of the bound variable and the
nonexpansiveness of truth-value suprema and infima.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.parameterPseudoMetricSpace MultiStructure.rowNonempty
  MultiStructure.parameterNonempty

universe u v w

namespace MultiFormula

/-- The product of the finite row- and parameter-assignment spaces. -/
abbrev Assignment {Symbol : Type w} (M : MultiStructure.{u, v, w} Symbol)
    (rowVars parameterVars : ℕ) :=
  (Fin rowVars → M.Row) × (Fin parameterVars → M.Parameter)

/-- Formula evaluation as a function on the combined assignment space. -/
def assignmentValue {Symbol : Type w} {rowVars parameterVars : ℕ}
    (formula : MultiFormula Symbol rowVars parameterVars)
    (M : MultiStructure.{u, v, w} Symbol) :
    Assignment M rowVars parameterVars → TruthValue :=
  fun assignment => formula.realize M assignment.1 assignment.2

/-- Adding the same leading row variable to two assignments does not enlarge
their distance. -/
theorem dist_cons_row_assignment_le
    {Symbol : Type w} {rowVars parameterVars : ℕ}
    (M : MultiStructure.{u, v, w} Symbol) (x : M.Row)
    (first second : Assignment M rowVars parameterVars) :
    dist ((Fin.cons x first.1, first.2) :
      Assignment M (rowVars + 1) parameterVars)
      ((Fin.cons x second.1, second.2) :
        Assignment M (rowVars + 1) parameterVars) ≤
      dist first second := by
  rw [Prod.dist_eq, Prod.dist_eq, max_le_iff]
  constructor
  · refine (dist_pi_le_iff
      ((dist_nonneg : 0 ≤ dist first.1 second.1).trans
        (le_max_left _ _))).2 fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simpa using
        (dist_le_pi_dist first.1 second.1 j).trans (le_max_left _ _)
  · exact le_max_right _ _

/-- Adding the same leading parameter variable to two assignments does not
enlarge their distance. -/
theorem dist_cons_parameter_assignment_le
    {Symbol : Type w} {rowVars parameterVars : ℕ}
    (M : MultiStructure.{u, v, w} Symbol) (y : M.Parameter)
    (first second : Assignment M rowVars parameterVars) :
    dist ((first.1, Fin.cons y first.2) :
      Assignment M rowVars (parameterVars + 1))
      ((second.1, Fin.cons y second.2) :
        Assignment M rowVars (parameterVars + 1)) ≤
      dist first second := by
  rw [Prod.dist_eq, Prod.dist_eq, max_le_iff]
  constructor
  · exact le_max_left _ _
  · refine (dist_pi_le_iff
      ((dist_nonneg : 0 ≤ dist first.1 second.1).trans
        (le_max_left _ _))).2 fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simpa using
        (dist_le_pi_dist first.2 second.2 j).trans (le_max_right _ _)

/-- Every continuous-logic formula is uniformly continuous in all its free
assignments. -/
theorem uniformContinuous_assignmentValue
    {Symbol : Type w} {rowVars parameterVars : ℕ}
    (formula : MultiFormula Symbol rowVars parameterVars)
    (M : MultiStructure.{u, v, w} Symbol) :
    UniformContinuous (formula.assignmentValue M) := by
  induction formula with
  | predicate symbol row parameter =>
      exact (M.predicate_uniformContinuous symbol).comp
        (((Pi.uniformContinuous_proj (fun _ : Fin _ => M.Row) row).comp
          uniformContinuous_fst).prodMk
          ((Pi.uniformContinuous_proj (fun _ : Fin _ => M.Parameter) parameter).comp
            uniformContinuous_snd))
  | constant value =>
      exact uniformContinuous_const
  | connective connective formulas induction =>
      exact connective.uniformContinuous.comp
        (uniformContinuous_pi.mpr fun coordinate => induction coordinate)
  | iSupRow formula induction =>
      rw [Metric.uniformContinuous_iff]
      rw [Metric.uniformContinuous_iff] at induction
      intro ε hε
      obtain ⟨δ, hδ, hchild⟩ := induction (ε / 2) (half_pos hε)
      refine ⟨δ, hδ, fun first second hdist => ?_⟩
      have hbound := abs_coe_iSup_sub_coe_iSup_le
        (fun x => formula.realize M (Fin.cons x first.1) first.2)
        (fun x => formula.realize M (Fin.cons x second.1) second.2)
        (ε := ε / 2) (fun x => by
          have hx := hchild
            ((dist_cons_row_assignment_le M x first second).trans_lt hdist)
          simpa [assignmentValue, Real.dist_eq] using hx.le)
      have hdist' :
          dist ((MultiFormula.iSupRow formula).assignmentValue M first)
            ((MultiFormula.iSupRow formula).assignmentValue M second) ≤ ε / 2 := by
        simpa [assignmentValue, MultiFormula.realize, Real.dist_eq] using hbound
      exact hdist'.trans_lt (half_lt_self hε)
  | iInfRow formula induction =>
      rw [Metric.uniformContinuous_iff]
      rw [Metric.uniformContinuous_iff] at induction
      intro ε hε
      obtain ⟨δ, hδ, hchild⟩ := induction (ε / 2) (half_pos hε)
      refine ⟨δ, hδ, fun first second hdist => ?_⟩
      have hbound := abs_coe_iInf_sub_coe_iInf_le
        (fun x => formula.realize M (Fin.cons x first.1) first.2)
        (fun x => formula.realize M (Fin.cons x second.1) second.2)
        (ε := ε / 2) (fun x => by
          have hx := hchild
            ((dist_cons_row_assignment_le M x first second).trans_lt hdist)
          simpa [assignmentValue, Real.dist_eq] using hx.le)
      have hdist' :
          dist ((MultiFormula.iInfRow formula).assignmentValue M first)
            ((MultiFormula.iInfRow formula).assignmentValue M second) ≤ ε / 2 := by
        simpa [assignmentValue, MultiFormula.realize, Real.dist_eq] using hbound
      exact hdist'.trans_lt (half_lt_self hε)
  | iSupParameter formula induction =>
      rw [Metric.uniformContinuous_iff]
      rw [Metric.uniformContinuous_iff] at induction
      intro ε hε
      obtain ⟨δ, hδ, hchild⟩ := induction (ε / 2) (half_pos hε)
      refine ⟨δ, hδ, fun first second hdist => ?_⟩
      have hbound := abs_coe_iSup_sub_coe_iSup_le
        (fun y => formula.realize M first.1 (Fin.cons y first.2))
        (fun y => formula.realize M second.1 (Fin.cons y second.2))
        (ε := ε / 2) (fun y => by
          have hy := hchild
            ((dist_cons_parameter_assignment_le M y first second).trans_lt hdist)
          simpa [assignmentValue, Real.dist_eq] using hy.le)
      have hdist' :
          dist ((MultiFormula.iSupParameter formula).assignmentValue M first)
            ((MultiFormula.iSupParameter formula).assignmentValue M second) ≤ ε / 2 := by
        simpa [assignmentValue, MultiFormula.realize, Real.dist_eq] using hbound
      exact hdist'.trans_lt (half_lt_self hε)
  | iInfParameter formula induction =>
      rw [Metric.uniformContinuous_iff]
      rw [Metric.uniformContinuous_iff] at induction
      intro ε hε
      obtain ⟨δ, hδ, hchild⟩ := induction (ε / 2) (half_pos hε)
      refine ⟨δ, hδ, fun first second hdist => ?_⟩
      have hbound := abs_coe_iInf_sub_coe_iInf_le
        (fun y => formula.realize M first.1 (Fin.cons y first.2))
        (fun y => formula.realize M second.1 (Fin.cons y second.2))
        (ε := ε / 2) (fun y => by
          have hy := hchild
            ((dist_cons_parameter_assignment_le M y first second).trans_lt hdist)
          simpa [assignmentValue, Real.dist_eq] using hy.le)
      have hdist' :
          dist ((MultiFormula.iInfParameter formula).assignmentValue M first)
            ((MultiFormula.iInfParameter formula).assignmentValue M second) ≤ ε / 2 := by
        simpa [assignmentValue, MultiFormula.realize, Real.dist_eq] using hbound
      exact hdist'.trans_lt (half_lt_self hε)

/-- Formula evaluation is continuous in all free assignments. -/
theorem continuous_assignmentValue
    {Symbol : Type w} {rowVars parameterVars : ℕ}
    (formula : MultiFormula Symbol rowVars parameterVars)
    (M : MultiStructure.{u, v, w} Symbol) :
    Continuous (formula.assignmentValue M) :=
  (formula.uniformContinuous_assignmentValue M).continuous

end MultiFormula

end

end NormFormula.ContinuousLogic
