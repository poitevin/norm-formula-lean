import NormFormula.ContinuousLogic.BanachBallCompactness
import NormFormula.ContinuousLogic.BanachBallTarskiVaught

/-!
# Separable typed ball structures retaining infinite IP

An infinite typed ball-formula witness consists of a countable row sequence
and one parameter for each finite disjoint prescription.  These points form a
countable sortwise seed for the ball-sorted Tarski--Vaught construction.  Its
closed limit is separable in every rational-radius sort, has the same complete
typed theory as the ambient structure, and retains the original witness with
the same thresholds.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Set TopologicalSpace

universe u w

namespace BallFormula

/-- A finite pair of disjoint sets of row indices, used to choose one IP
parameter for every finite prescription. -/
def BallIPPrescription :=
  { pair : Finset ℕ × Finset ℕ // Disjoint pair.1 pair.2 }

noncomputable instance ballIPPrescription_countable :
    Countable BallIPPrescription := by
  unfold BallIPPrescription
  infer_instance

/-- The sortwise stage-zero indices containing the rows and chosen parameters
of one infinite IP witness.  Equality proofs place each family only in its
specified rational-radius sort. -/
def BallIPSeedIndex
    (rowRadius parameterRadius radius : ℚ≥0) : Type (max u w) :=
  ULift.{max u w}
    ((ℕ × PLift (rowRadius = radius)) ⊕
      (BallIPPrescription × PLift (parameterRadius = radius)))

noncomputable instance ballIPSeedIndex_countable
    (rowRadius parameterRadius radius : ℚ≥0) :
    Countable (BallIPSeedIndex.{u, w} rowRadius parameterRadius radius) := by
  unfold BallIPSeedIndex
  infer_instance

/-- The closed elementary substructure generated from an IP witness can
also retain a prescribed sequence in each radius sort. -/
theorem exists_separableElementaryIPSubstructure_containing
    {Symbol : Type w} [Encodable Symbol]
    {symbolRadius : Symbol → ℚ≥0}
    {rowRadius parameterRadius : ℚ≥0}
    {M : BallStructure.{u, w} Symbol symbolRadius}
    {formula : BallFormula Symbol symbolRadius
      (![rowRadius, parameterRadius] : BallContext 2)}
    {low high : ℝ}
    (seed : ∀ radius, ℕ → M.Ball radius)
    (hIP : formula.HasInfiniteIPWitness M low high) :
    ∃ initial : BallWitnessIndexing M,
      (∀ radius k, seed radius k ∈ initial.LimitCarrier radius) ∧
      formula.HasInfiniteIPWitness initial.limitBallStructure low high := by
  classical
  obtain ⟨sourceRows, hsource⟩ := hIP
  have hexistsParameter : ∀ prescription : BallIPPrescription,
      ∃ parameter : M.Ball parameterRadius,
        (∀ i ∈ prescription.1.1,
          formula.binaryValue M (sourceRows i) parameter ≤ low) ∧
        (∀ i ∈ prescription.1.2,
          high ≤ formula.binaryValue M (sourceRows i) parameter) := by
    intro prescription
    exact hsource prescription.1.1 prescription.1.2 prescription.2
  choose sourceParameter hsourceParameter using hexistsParameter
  let initial : BallWitnessIndexing M := {
    Index := fun radius ↦ BallIPSeedIndex.{u, w} rowRadius parameterRadius radius ⊕ ℕ
    indexCountable := fun radius ↦ inferInstance
    indexMap := fun radius index ↦
      match index with
      | .inl ⟨.inl row⟩ => by
          rw [← row.2.down]
          exact sourceRows row.1
      | .inl ⟨.inr parameter⟩ => by
          rw [← parameter.2.down]
          exact sourceParameter parameter.1
      | .inr k => seed radius k }
  let target := initial.limitBallStructure
  refine ⟨initial, ?_, ?_⟩
  · intro radius k
    exact (initial.limitPoint radius ⟨0, Sum.inr k⟩).property
  let targetRows : ℕ → target.Ball rowRadius := fun i ↦
    initial.limitPoint rowRadius
      ⟨0, Sum.inl (ULift.up (Sum.inl ⟨i, ⟨rfl⟩⟩))⟩
  refine ⟨targetRows, ?_⟩
  intro E F hdisjoint
  let prescription : BallIPPrescription := ⟨(E, F), hdisjoint⟩
  let targetParameter : target.Ball parameterRadius :=
    initial.limitPoint parameterRadius
      ⟨0, Sum.inl (ULift.up (Sum.inr ⟨prescription, ⟨rfl⟩⟩))⟩
  have hbinaryValue (i : ℕ) :
      formula.binaryValue target (targetRows i) targetParameter =
        formula.binaryValue M (sourceRows i) (sourceParameter prescription) := by
    have hvalue := congrArg (fun value : TruthValue ↦ (value : ℝ))
      (initial.ballFormula_realize_limitBallStructure_eq_ambient formula
        (Fin.cons (targetRows i)
          (Fin.cons targetParameter (fun j : Fin 0 ↦ nomatch j))))
    have hassignment :
        initial.includeLimitBallAssignment
            ((Fin.cons (targetRows i)
              (Fin.cons targetParameter (fun j : Fin 0 ↦ nomatch j))) :
              BallTerm.Assignment initial.limitRationalBallSystem
                (![rowRadius, parameterRadius] : BallContext 2)) =
          (Fin.cons (sourceRows i)
            (Fin.cons (sourceParameter prescription)
              (fun j : Fin 0 ↦ nomatch j)) :
            BallTerm.Assignment M.toRationalBallSystem
              (![rowRadius, parameterRadius] : BallContext 2)) := by
      funext j
      fin_cases j <;> rfl
    rw [hassignment] at hvalue
    exact hvalue
  refine ⟨targetParameter, ?_, ?_⟩
  · intro i hi
    rw [hbinaryValue]
    exact (hsourceParameter prescription).1 i hi
  · intro i hi
    rw [hbinaryValue]
    exact (hsourceParameter prescription).2 i hi

/-- A fixed infinite typed IP witness is retained in a same-theory closed
substructure whose every rational-radius sort is separable. -/
theorem exists_separableElementaryIPSubstructure
    {Symbol : Type w} [Encodable Symbol]
    {symbolRadius : Symbol → ℚ≥0}
    {rowRadius parameterRadius : ℚ≥0}
    {M : BallStructure.{u, w} Symbol symbolRadius}
    {formula : BallFormula Symbol symbolRadius
      (![rowRadius, parameterRadius] : BallContext 2)}
    {low high : ℝ}
    (hIP : formula.HasInfiniteIPWitness M low high) :
    ∃ N : BallStructure.{u, w} Symbol symbolRadius,
      BallSameCompleteTheory M N ∧
      (∀ radius : ℚ≥0, IsSeparable (Set.univ : Set (N.Ball radius))) ∧
      formula.HasInfiniteIPWitness N low high := by
  obtain ⟨initial, _, hWitness⟩ :=
    exists_separableElementaryIPSubstructure_containing (fun r _ ↦ M.zero r) hIP
  exact ⟨initial.limitBallStructure,
    fun sentence ↦ (initial.limitBallStructure_sameCompleteTheory_ambient sentence).symm,
    initial.limitCarrier_isSeparable, hWitness⟩

/-- Finite patterns at specified thresholds therefore produce a same-theory
sortwise separable model retaining an infinite witness at those exact
thresholds. -/
theorem exists_separableModel_of_finitePatterns
    {Symbol : Type w} [Encodable Symbol]
    {symbolRadius : Symbol → ℚ≥0}
    {rowRadius parameterRadius : ℚ≥0}
    (M : BallStructure.{u, w} Symbol symbolRadius)
    (formula : BallFormula Symbol symbolRadius
      (![rowRadius, parameterRadius] : BallContext 2))
    (low high : ℝ)
    (hpatterns : formula.HasFiniteIPPatternsInEveryDimension M low high) :
    ∃ N : BallStructure.{u, w} Symbol symbolRadius,
      BallSameCompleteTheory M N ∧
      (∀ radius : ℚ≥0, IsSeparable (Set.univ : Set (N.Ball radius))) ∧
      formula.HasInfiniteIPWitness N low high := by
  obtain ⟨ambient, hTheory, hWitness⟩ :=
    exists_sameTheory_infiniteWitness_of_finitePatterns
      M formula low high hpatterns
  obtain ⟨target, hTargetTheory, hSeparable, hTargetWitness⟩ :=
    exists_separableElementaryIPSubstructure hWitness
  exact ⟨target,
    (fun sentence ↦ (hTheory sentence).trans (hTargetTheory sentence)),
    hSeparable, hTargetWitness⟩

/-- Complete-theory IP for a typed binary ball formula therefore has a
same-theory witnessing model separable in every rational-radius sort. -/
theorem exists_separableModel_of_hasIPInCompleteTheory
    {Symbol : Type w} [Encodable Symbol]
    {symbolRadius : Symbol → ℚ≥0}
    {rowRadius parameterRadius : ℚ≥0}
    {M : BallStructure.{u, w} Symbol symbolRadius}
    {formula : BallFormula Symbol symbolRadius
      (![rowRadius, parameterRadius] : BallContext 2)}
    (hIP : formula.HasIPInCompleteTheory M) :
    ∃ N : BallStructure.{u, w} Symbol symbolRadius,
      BallSameCompleteTheory M N ∧
      (∀ radius : ℚ≥0, IsSeparable (Set.univ : Set (N.Ball radius))) ∧
      ∃ low high : ℝ, low < high ∧
        formula.HasInfiniteIPWitness N low high := by
  obtain ⟨ambient, hTheory, low, high, hgap, hwitness⟩ := hIP
  obtain ⟨target, hTargetTheory, hSeparable, hTargetWitness⟩ :=
    exists_separableElementaryIPSubstructure hwitness
  exact ⟨target,
    (fun sentence ↦ (hTheory sentence).trans (hTargetTheory sentence)), hSeparable,
    low, high, hgap, hTargetWitness⟩

end BallFormula

end

end NormFormula.ContinuousLogic
