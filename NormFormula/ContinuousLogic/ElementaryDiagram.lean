import Mathlib.Topology.Order.Lattice
import NormFormula.ContinuousLogic.AbsoluteDifference
import NormFormula.ContinuousLogic.MultiTheoryIP

/-!
# Finite fragments of an elementary diagram

A constant instance of a formula is represented by the formula together with
the finite tuples of named row and parameter elements substituted for its free
variables.  A finite diagram fragment packages finitely many formulae over one
such tuple.  This is equivalent to using a language with constants for the
tuple, while reusing the existing formula syntax.

The main theorem proves approximate finite satisfiability: a finite fragment
from one structure can be realized, to any positive tolerance, in every
structure with the same complete theory.  Its expansion form says that a
finite reduct diagram is approximately satisfiable together with the complete
theory of a distinguished expansion.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open scoped Topology

universe u v u' v' w z

attribute [local instance] MultiStructure.rowNonempty
  MultiStructure.parameterNonempty

/-- The largest absolute deviation from a finite vector of target truth
values.  The empty maximum is the zero truth value. -/
def finiteMaxDeviationTruth {conditionCount : ℕ}
    (targets values : Fin conditionCount → TruthValue) : TruthValue :=
  Finset.univ.sup fun i ↦ absoluteDifferenceTruth ![values i, targets i]

/-- Finite maximum of absolute deviations as a continuous connective. -/
def finiteMaxDeviationConnective {conditionCount : ℕ}
    (targets : Fin conditionCount → TruthValue) :
    Connective conditionCount where
  toFun := finiteMaxDeviationTruth targets
  continuous_toFun := by
    apply Continuous.finset_sup_apply
    intro i hi
    apply absoluteDifferenceConnective.continuous_toFun.comp
    apply continuous_pi
    intro j
    fin_cases j
    · exact continuous_apply i
    · exact continuous_const

/-- Each individual deviation is bounded by the finite maximum. -/
theorem absoluteDifferenceTruth_le_finiteMaxDeviationTruth
    {conditionCount : ℕ}
    (targets values : Fin conditionCount → TruthValue)
    (i : Fin conditionCount) :
    absoluteDifferenceTruth ![values i, targets i] ≤
      finiteMaxDeviationTruth targets values :=
  Finset.le_sup (s := Finset.univ)
    (f := fun j ↦ absoluteDifferenceTruth ![values j, targets j])
    (Finset.mem_univ i)

/-- The finite maximum deviation of a vector from itself is zero. -/
@[simp]
theorem finiteMaxDeviationTruth_self {conditionCount : ℕ}
    (targets : Fin conditionCount → TruthValue) :
    finiteMaxDeviationTruth targets targets = zeroTruthValue := by
  apply le_antisymm
  · refine Finset.sup_le ?_
    intro i hi
    apply le_of_eq
    apply Subtype.ext
    simp [absoluteDifferenceTruth, zeroTruthValue]
  · exact (finiteMaxDeviationTruth targets targets).2.1

namespace MultiFormula

/-- Bind all free row variables by infimum quantifiers. -/
def iInfAllRows {Symbol : Type w} {parameterVars : ℕ} :
    {rowVars : ℕ} →
      MultiFormula Symbol rowVars parameterVars →
        MultiFormula Symbol 0 parameterVars
  | 0, φ => φ
  | _ + 1, φ => iInfAllRows (.iInfRow φ)

/-- Bind all free parameter variables by infimum quantifiers. -/
def iInfAllParameters {Symbol : Type w} :
    {parameterVars : ℕ} →
      MultiFormula Symbol 0 parameterVars → MultiSentence Symbol
  | 0, φ => φ
  | _ + 1, φ => iInfAllParameters (.iInfParameter φ)

/-- Close every free variable of a formula using infimum quantifiers. -/
def infClosure {Symbol : Type w} {rowVars parameterVars : ℕ}
    (φ : MultiFormula Symbol rowVars parameterVars) : MultiSentence Symbol :=
  iInfAllParameters (iInfAllRows φ)

/-- The infimum closure in the row variables is below every concrete row
assignment. -/
theorem iInfAllRows_realize_le
    {Symbol : Type w} {parameterVars : ℕ} :
    ∀ {rowVars : ℕ} (φ : MultiFormula Symbol rowVars parameterVars)
      (M : MultiStructure.{u, v, w} Symbol)
      (rows : Fin rowVars → M.Row)
      (parameters : Fin parameterVars → M.Parameter),
      (iInfAllRows φ).realize M Fin.elim0 parameters ≤
        φ.realize M rows parameters
  | 0, φ, M, rows, parameters => by
      have hrows : rows = Fin.elim0 := Subsingleton.elim _ _
      subst rows
      exact le_rfl
  | _ + 1, φ, M, rows, parameters => by
      calc
        (iInfAllRows φ).realize M Fin.elim0 parameters ≤
            (MultiFormula.iInfRow φ).realize M (Fin.tail rows) parameters :=
          iInfAllRows_realize_le (MultiFormula.iInfRow φ) M
            (Fin.tail rows) parameters
        _ ≤ φ.realize M rows parameters := by
          have h := iInf_le
            (fun x : M.Row ↦ φ.realize M (Fin.cons x (Fin.tail rows)) parameters)
            (rows 0)
          simpa only [Fin.cons_self_tail] using h

/-- The infimum closure in the parameter variables is below every concrete
parameter assignment. -/
theorem iInfAllParameters_realize_le
    {Symbol : Type w} :
    ∀ {parameterVars : ℕ} (φ : MultiFormula Symbol 0 parameterVars)
      (M : MultiStructure.{u, v, w} Symbol)
      (parameters : Fin parameterVars → M.Parameter),
      (iInfAllParameters φ).realize M Fin.elim0 Fin.elim0 ≤
        φ.realize M Fin.elim0 parameters
  | 0, φ, M, parameters => by
      have hparameters : parameters = Fin.elim0 := Subsingleton.elim _ _
      subst parameters
      exact le_rfl
  | _ + 1, φ, M, parameters => by
      calc
        (iInfAllParameters φ).realize M Fin.elim0 Fin.elim0 ≤
            (MultiFormula.iInfParameter φ).realize M Fin.elim0
              (Fin.tail parameters) :=
          iInfAllParameters_realize_le (MultiFormula.iInfParameter φ) M
            (Fin.tail parameters)
        _ ≤ φ.realize M Fin.elim0 parameters := by
          have h := iInf_le
            (fun y : M.Parameter ↦
              φ.realize M Fin.elim0 (Fin.cons y (Fin.tail parameters)))
            (parameters 0)
          simpa only [Fin.cons_self_tail] using h

/-- The fully closed infimum sentence is below the value at every assignment. -/
theorem infClosure_realize_le
    {Symbol : Type w} {rowVars parameterVars : ℕ}
    (φ : MultiFormula Symbol rowVars parameterVars)
    (M : MultiStructure.{u, v, w} Symbol)
    (rows : Fin rowVars → M.Row)
    (parameters : Fin parameterVars → M.Parameter) :
    (infClosure φ).realize M Fin.elim0 Fin.elim0 ≤
      φ.realize M rows parameters :=
  (iInfAllParameters_realize_le (iInfAllRows φ) M parameters).trans
    (iInfAllRows_realize_le φ M rows parameters)

/-- If the value of a row-infimum closure is below a real threshold, some row
assignment already has value below that threshold. -/
theorem exists_rows_realize_lt_of_iInfAllRows_lt
    {Symbol : Type w} {parameterVars : ℕ} :
    ∀ {rowVars : ℕ} (φ : MultiFormula Symbol rowVars parameterVars)
      (M : MultiStructure.{u, v, w} Symbol)
      (parameters : Fin parameterVars → M.Parameter) (ε : ℝ),
      (((iInfAllRows φ).realize M Fin.elim0 parameters : TruthValue) : ℝ) < ε →
        ∃ rows : Fin rowVars → M.Row,
          ((φ.realize M rows parameters : TruthValue) : ℝ) < ε
  | 0, φ, M, parameters, ε => fun h ↦ ⟨Fin.elim0, h⟩
  | _ + 1, φ, M, parameters, ε => by
      intro h
      obtain ⟨tail, htail⟩ :=
        exists_rows_realize_lt_of_iInfAllRows_lt
          (MultiFormula.iInfRow φ) M parameters ε h
      change (((⨅ x : M.Row,
        φ.realize M (Fin.cons x tail) parameters : TruthValue)) : ℝ) < ε at htail
      rw [Set.Icc.coe_iInf zero_le_one] at htail
      obtain ⟨x, hx⟩ := exists_lt_of_ciInf_lt htail
      exact ⟨Fin.cons x tail, hx⟩

/-- Parameter analogue of
`exists_rows_realize_lt_of_iInfAllRows_lt`. -/
theorem exists_parameters_realize_lt_of_iInfAllParameters_lt
    {Symbol : Type w} :
    ∀ {parameterVars : ℕ} (φ : MultiFormula Symbol 0 parameterVars)
      (M : MultiStructure.{u, v, w} Symbol) (ε : ℝ),
      (((iInfAllParameters φ).realize M Fin.elim0 Fin.elim0 :
        TruthValue) : ℝ) < ε →
        ∃ parameters : Fin parameterVars → M.Parameter,
          ((φ.realize M Fin.elim0 parameters : TruthValue) : ℝ) < ε
  | 0, φ, M, ε => fun h ↦ ⟨Fin.elim0, h⟩
  | _ + 1, φ, M, ε => by
      intro h
      obtain ⟨tail, htail⟩ :=
        exists_parameters_realize_lt_of_iInfAllParameters_lt
          (MultiFormula.iInfParameter φ) M ε h
      change (((⨅ y : M.Parameter,
        φ.realize M Fin.elim0 (Fin.cons y tail) : TruthValue)) : ℝ) < ε at htail
      rw [Set.Icc.coe_iInf zero_le_one] at htail
      obtain ⟨y, hy⟩ := exists_lt_of_ciInf_lt htail
      exact ⟨Fin.cons y tail, hy⟩

end MultiFormula

/-- A finite constant-enriched fragment of the elementary diagram of `N`.
The tuple entries are the named constants, and `formulas` are the finitely many
conditions imposed on that common tuple. -/
structure FiniteElementaryDiagramFragment {Symbol : Type w}
    (N : MultiStructure.{u, v, w} Symbol) where
  rowVars : ℕ
  parameterVars : ℕ
  conditionCount : ℕ
  formulas : Fin conditionCount →
    MultiFormula Symbol rowVars parameterVars
  rows : Fin rowVars → N.Row
  parameters : Fin parameterVars → N.Parameter

namespace FiniteElementaryDiagramFragment

variable {Symbol : Type w} {N : MultiStructure.{u, v, w} Symbol}

/-- The exact target truth values named by a finite diagram fragment. -/
def targets (fragment : FiniteElementaryDiagramFragment N) :
    Fin fragment.conditionCount → TruthValue :=
  fun i ↦ (fragment.formulas i).realize N fragment.rows fragment.parameters

/-- One formula measuring the maximum error in a finite diagram fragment. -/
def deviationFormula (fragment : FiniteElementaryDiagramFragment N) :
    MultiFormula Symbol fragment.rowVars fragment.parameterVars :=
  .connective (finiteMaxDeviationConnective fragment.targets) fragment.formulas

/-- The sentence asserting that the finite fragment is approximately
realizable. -/
def satisfiabilitySentence (fragment : FiniteElementaryDiagramFragment N) :
    MultiSentence Symbol :=
  MultiFormula.infClosure fragment.deviationFormula

/-- The named tuple in `N` realizes its own finite diagram with zero error. -/
@[simp]
theorem deviationFormula_realize_named
    (fragment : FiniteElementaryDiagramFragment N) :
    fragment.deviationFormula.realize N fragment.rows fragment.parameters =
      zeroTruthValue := by
  change finiteMaxDeviationTruth fragment.targets fragment.targets =
    zeroTruthValue
  exact finiteMaxDeviationTruth_self fragment.targets

/-- Consequently the satisfiability sentence of the fragment has value zero
in `N`. -/
@[simp]
theorem satisfiabilitySentence_value
    (fragment : FiniteElementaryDiagramFragment N) :
    fragment.satisfiabilitySentence.value N = zeroTruthValue := by
  apply le_antisymm
  · exact (MultiFormula.infClosure_realize_le fragment.deviationFormula N
      fragment.rows fragment.parameters).trans_eq
        fragment.deviationFormula_realize_named
  · exact (fragment.satisfiabilitySentence.value N).2.1

/-- Approximate finite satisfiability of the constant-enriched elementary
diagram in every structure with the same complete theory. -/
theorem approximately_realized_of_sameCompleteTheory
    {M : MultiStructure.{u', v', w} Symbol}
    (hTheory : MultiSameCompleteTheory M N)
    (fragment : FiniteElementaryDiagramFragment N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ rows : Fin fragment.rowVars → M.Row,
      ∃ parameters : Fin fragment.parameterVars → M.Parameter,
        ∀ i : Fin fragment.conditionCount,
          |(((fragment.formulas i).realize M rows parameters :
              TruthValue) : ℝ) -
            ((fragment.targets i : TruthValue) : ℝ)| < ε := by
  have hsentence : fragment.satisfiabilitySentence.value M =
      zeroTruthValue := by
    calc
      fragment.satisfiabilitySentence.value M =
          fragment.satisfiabilitySentence.value N :=
        hTheory fragment.satisfiabilitySentence
      _ = zeroTruthValue := fragment.satisfiabilitySentence_value
  have hlt : (((fragment.satisfiabilitySentence.value M : TruthValue) : ℝ)) < ε := by
    rw [hsentence]
    exact hε
  obtain ⟨parameters, hparameters⟩ :=
    MultiFormula.exists_parameters_realize_lt_of_iInfAllParameters_lt
      (MultiFormula.iInfAllRows fragment.deviationFormula) M ε hlt
  obtain ⟨rows, hrows⟩ :=
    MultiFormula.exists_rows_realize_lt_of_iInfAllRows_lt
      fragment.deviationFormula M parameters ε hparameters
  refine ⟨rows, parameters, ?_⟩
  intro i
  have hle := absoluteDifferenceTruth_le_finiteMaxDeviationTruth
    fragment.targets
    (fun j ↦ (fragment.formulas j).realize M rows parameters) i
  have hleReal :
      |(((fragment.formulas i).realize M rows parameters :
          TruthValue) : ℝ) - ((fragment.targets i : TruthValue) : ℝ)| ≤
        ((fragment.deviationFormula.realize M rows parameters :
          TruthValue) : ℝ) :=
    hle
  exact hleReal.trans_lt hrows

/-- Expansion form of finite satisfiability: every finite elementary-diagram
fragment of a same-theory reduct is approximately realized inside the
distinguished expansion itself.  Thus it is satisfiable together with every
sentence of the complete expansion theory. -/
theorem approximately_realized_in_expansion
    {Target : Type z} (f : Symbol → Target)
    (M : MultiStructure.{u', v', z} Target)
    (hTheory : MultiSameCompleteTheory (M.reduct f) N)
    (fragment : FiniteElementaryDiagramFragment N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ rows : Fin fragment.rowVars → M.Row,
      ∃ parameters : Fin fragment.parameterVars → M.Parameter,
        ∀ i : Fin fragment.conditionCount,
          |((((fragment.formulas i).map f).realize M rows parameters :
              TruthValue) : ℝ) -
            ((fragment.targets i : TruthValue) : ℝ)| < ε := by
  obtain ⟨rows, parameters, hrealize⟩ :=
    fragment.approximately_realized_of_sameCompleteTheory
      hTheory ε hε
  refine ⟨rows, parameters, ?_⟩
  intro i
  have hmap := congrArg (fun value : TruthValue ↦ (value : ℝ))
    (MultiFormula.realize_map_reduct f M (fragment.formulas i) rows parameters)
  change ((((fragment.formulas i).map f).realize M rows parameters :
      TruthValue) : ℝ) =
    (((fragment.formulas i).realize (M.reduct f) rows parameters :
      TruthValue) : ℝ) at hmap
  rw [hmap]
  exact hrealize i

end FiniteElementaryDiagramFragment

/-- The exact compactness principle needed after finite approximate
satisfiability of an elementary diagram has been established.  It says that
if every finite constant-enriched reduct fragment can be approximated inside
the distinguished expansion, then the whole reduct model embeds
formula-preservingly into a model of the complete expansion theory.

Separating this principle from finite satisfiability makes the remaining
compactness boundary explicit, rather than hiding it inside reduct transfer. -/
def ElementaryDiagramCompactness
    {Symbol : Type w} {Target : Type z}
    (f : Symbol → Target) (M : MultiStructure.{u, v, z} Target) : Prop :=
  ∀ N : MultiStructure.{u, v, w} Symbol,
    (∀ (fragment : FiniteElementaryDiagramFragment N) (ε : ℝ), 0 < ε →
      ∃ rows : Fin fragment.rowVars → M.Row,
        ∃ parameters : Fin fragment.parameterVars → M.Parameter,
          ∀ i : Fin fragment.conditionCount,
            |((((fragment.formulas i).map f).realize M rows parameters :
                TruthValue) : ℝ) -
              ((fragment.targets i : TruthValue) : ℝ)| < ε) →
      Nonempty (MultiStructure.SameTheoryReductEmbedding f M N)

/-- Elementary-diagram compactness, together with equality of complete reduct
theories, supplies the reduct-embedding property used by NIP transfer.  The
finite-satisfiability premise is discharged by
`approximately_realized_in_expansion`. -/
theorem hasSameTheoryReductEmbeddingProperty_of_elementaryDiagramCompactness
    {Symbol : Type w} {Target : Type z}
    (f : Symbol → Target) (M : MultiStructure.{u, v, z} Target)
    (hcompact : ElementaryDiagramCompactness f M) :
    M.HasSameTheoryReductEmbeddingProperty f := by
  intro N hTheory
  apply hcompact N
  intro fragment ε hε
  exact fragment.approximately_realized_in_expansion f M hTheory ε hε

end

end NormFormula.ContinuousLogic
