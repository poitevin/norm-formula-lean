import NormFormula.ContinuousLogic.BanachBallConnectiveRestriction

/-!
# Uniform continuity of typed ball-formula evaluation

Every typed ball formula is uniformly continuous in its finite dependent
assignment.  For a quantified formula, adding the same leading bound
variable does not enlarge assignment distance, and supremum or infimum of
uniformly close truth-value families remains uniformly close.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open scoped Topology

universe u w

namespace BallFormula

/-- Adding the same leading bound variable to two dependent assignments does
not enlarge their distance. -/
theorem dist_cons_assignment_le
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius)
    {n : ℕ} {context : BallContext n} (radius : ℚ≥0)
    (x : M.Ball radius)
    (first second : BallTerm.Assignment M.toRationalBallSystem context) :
    dist (Fin.cons x first : BallTerm.Assignment M.toRationalBallSystem
      (Fin.cons radius context))
      (Fin.cons x second : BallTerm.Assignment M.toRationalBallSystem
        (Fin.cons radius context)) ≤
      dist first second := by
  refine (dist_pi_le_iff dist_nonneg).2 fun i ↦ ?_
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simpa using dist_le_pi_dist first second j

/-- Evaluation of every typed ball formula is uniformly continuous in its
finite dependent assignment. -/
theorem realize_uniformContinuous
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n}
    (formula : BallFormula Symbol symbolRadius context)
    (M : BallStructure.{u, w} Symbol symbolRadius) :
    UniformContinuous (formula.realize M) := by
  induction formula with
  | distance left right =>
      exact distance_realize_uniformContinuous M left right
  | predicate symbol term =>
      exact predicate_realize_uniformContinuous M symbol term
  | constant value =>
      exact uniformContinuous_const
  | connective connective formulas induction =>
      exact connective.uniformContinuous.comp
        (uniformContinuous_pi.mpr fun coordinate ↦ induction coordinate)
  | iSup radius formula induction =>
      rw [Metric.uniformContinuous_iff]
      rw [Metric.uniformContinuous_iff] at induction
      intro ε hε
      obtain ⟨δ, hδ, hchild⟩ := induction (ε / 2) (half_pos hε)
      refine ⟨δ, hδ, fun first second hdist ↦ ?_⟩
      have hbound := abs_coe_iSup_sub_coe_iSup_le
        (fun x ↦ formula.realize M (Fin.cons x first))
        (fun x ↦ formula.realize M (Fin.cons x second))
        (ε := ε / 2) (fun x ↦ by
          have hx := hchild
            ((dist_cons_assignment_le M radius x first second).trans_lt hdist)
          simpa [Real.dist_eq] using hx.le)
      have hparent :
          dist ((BallFormula.iSup radius formula).realize M first)
            ((BallFormula.iSup radius formula).realize M second) ≤ ε / 2 := by
        simpa [BallFormula.realize, Real.dist_eq] using hbound
      exact hparent.trans_lt (half_lt_self hε)
  | iInf radius formula induction =>
      rw [Metric.uniformContinuous_iff]
      rw [Metric.uniformContinuous_iff] at induction
      intro ε hε
      obtain ⟨δ, hδ, hchild⟩ := induction (ε / 2) (half_pos hε)
      refine ⟨δ, hδ, fun first second hdist ↦ ?_⟩
      have hbound := abs_coe_iInf_sub_coe_iInf_le
        (fun x ↦ formula.realize M (Fin.cons x first))
        (fun x ↦ formula.realize M (Fin.cons x second))
        (ε := ε / 2) (fun x ↦ by
          have hx := hchild
            ((dist_cons_assignment_le M radius x first second).trans_lt hdist)
          simpa [Real.dist_eq] using hx.le)
      have hparent :
          dist ((BallFormula.iInf radius formula).realize M first)
            ((BallFormula.iInf radius formula).realize M second) ≤ ε / 2 := by
        simpa [BallFormula.realize, Real.dist_eq] using hbound
      exact hparent.trans_lt (half_lt_self hε)

/-- Evaluation of every typed ball formula is continuous in its finite
dependent assignment. -/
theorem realize_continuous
    {Symbol : Type w} {symbolRadius : Symbol → ℚ≥0}
    {n : ℕ} {context : BallContext n}
    (formula : BallFormula Symbol symbolRadius context)
    (M : BallStructure.{u, w} Symbol symbolRadius) :
    Continuous (formula.realize M) :=
  (formula.realize_uniformContinuous M).continuous

end BallFormula

end

end NormFormula.ContinuousLogic
