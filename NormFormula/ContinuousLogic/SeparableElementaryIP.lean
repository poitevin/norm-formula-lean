import NormFormula.ContinuousLogic.WitnessLimitElementarity
import NormFormula.ContinuousLogic.SeparableIPCore

/-!
# Separable elementary structures retaining infinite IP

Starting from one infinite witness, use its countable row sequence and one
chosen parameter for each finite disjoint prescription as the initial witness
indexing. The closed Tarski--Vaught limit is separable, has the same complete
theory as the ambient structure, and retains the original thresholds.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Set TopologicalSpace

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.parameterPseudoMetricSpace MultiStructure.rowNonempty
  MultiStructure.parameterNonempty

universe u v w

namespace MultiFormula

/-- A fixed infinite IP witness in a many-predicate structure is contained in
a separable elementary closed substructure with the same thresholds. -/
theorem exists_separableElementaryIPSubstructure
    {Symbol : Type w} [Encodable Symbol]
    {M : MultiStructure.{u, v, w} Symbol}
    {formula : MultiFormula Symbol 1 1} {low high : ℝ}
    (hIP : HasInfiniteIPWitness M formula low high) :
    ∃ N : MultiStructure.{u, v, w} Symbol,
      MultiSameCompleteTheory M N ∧
      IsSeparable (Set.univ : Set N.Row) ∧
      IsSeparable (Set.univ : Set N.Parameter) ∧
      HasInfiniteIPWitness N formula low high := by
  classical
  obtain ⟨sourceRows, hsource⟩ := hIP
  have hexistsParameter : ∀ prescription : DisjointFiniteNatPair,
      ∃ parameter : M.Parameter,
        (∀ i ∈ prescription.1.1,
          formula.binaryValue M (sourceRows i) parameter ≤ low) ∧
        (∀ i ∈ prescription.1.2,
          high ≤ formula.binaryValue M (sourceRows i) parameter) := by
    intro prescription
    exact hsource prescription.1.1 prescription.1.2 prescription.2
  choose sourceParameter hsourceParameter using hexistsParameter
  let initial : WitnessIndexing M := {
    RowIndex := ULift.{max u v w} ℕ
    ParameterIndex := ULift.{max u v w} DisjointFiniteNatPair
    rowCountable := inferInstance
    parameterCountable := inferInstance
    rowMap := fun index => sourceRows index.down
    parameterMap := fun index => sourceParameter index.down }
  letI : Nonempty initial.RowIndex := inferInstance
  let emptyPrescription : DisjointFiniteNatPair :=
    ⟨(∅, ∅), by simp⟩
  letI : Nonempty initial.ParameterIndex :=
    ⟨ULift.up emptyPrescription⟩
  let target := initial.limitStructure
  refine ⟨target, (initial.limitStructure_sameCompleteTheory).symm,
    initial.limitCarriers_isSeparable.1,
    initial.limitCarriers_isSeparable.2, ?_⟩
  let targetRows : ℕ → target.Row := fun i =>
    initial.limitRowPoint ⟨0, ULift.up i⟩
  refine ⟨targetRows, ?_⟩
  intro E F hdisjoint
  let prescription : DisjointFiniteNatPair := ⟨(E, F), hdisjoint⟩
  let targetParameter : target.Parameter :=
    initial.limitParameterPoint ⟨0, ULift.up prescription⟩
  refine ⟨targetParameter, ?_, ?_⟩
  · intro i hi
    have hvalue := congrArg (fun value : TruthValue => (value : ℝ))
      (initial.formula_realize_limitStructure_eq_ambient formula
        (fun _ => targetRows i) (fun _ => targetParameter))
    change formula.binaryValue target (targetRows i) targetParameter =
      formula.binaryValue M (sourceRows i) (sourceParameter prescription) at hvalue
    rw [hvalue]
    exact (hsourceParameter prescription).1 i hi
  · intro i hi
    have hvalue := congrArg (fun value : TruthValue => (value : ℝ))
      (initial.formula_realize_limitStructure_eq_ambient formula
        (fun _ => targetRows i) (fun _ => targetParameter))
    change formula.binaryValue target (targetRows i) targetParameter =
      formula.binaryValue M (sourceRows i) (sourceParameter prescription) at hvalue
    rw [hvalue]
    exact (hsourceParameter prescription).2 i hi

/-- Theory-level IP has a separable same-theory witnessing model. -/
theorem exists_separableModel_of_hasIPInCompleteTheory
    {Symbol : Type w} [Encodable Symbol]
    {M : MultiStructure.{u, v, w} Symbol}
    {formula : MultiFormula Symbol 1 1}
    (hIP : HasIPInCompleteTheory M formula) :
    ∃ N : MultiStructure.{u, v, w} Symbol,
      MultiSameCompleteTheory M N ∧
      IsSeparable (Set.univ : Set N.Row) ∧
      IsSeparable (Set.univ : Set N.Parameter) ∧
      ∃ low high : ℝ, low < high ∧
        HasInfiniteIPWitness N formula low high := by
  obtain ⟨ambient, hTheory, low, high, hgap, hwitness⟩ := hIP
  obtain ⟨target, hTargetTheory, hRowSeparable, hParameterSeparable,
    hTargetWitness⟩ := exists_separableElementaryIPSubstructure hwitness
  exact ⟨target, hTheory.trans hTargetTheory, hRowSeparable,
    hParameterSeparable, low, high, hgap, hTargetWitness⟩

end MultiFormula

end

end NormFormula.ContinuousLogic
