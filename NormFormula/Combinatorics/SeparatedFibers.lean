import NormFormula.Combinatorics.StrongShatteringCount

/-!
# Coordinate fibers of two-separated finite classes

The finite-range packing recurrence partitions a finite class of functions by
their value at one coordinate. A fiber remains pairwise two-separated after
that coordinate is deleted. If two fibers at levels separated by at least two
strongly shatter a common threshold pair, the original class also strongly
shatters the pair with the fiber coordinate inserted.
-/

namespace NormFormula

/-- Pairwise separation by two integer levels on a specified finite row set. -/
def IsPairwiseTwoSeparatedOn
    {Row : Type*} [DecidableEq Row]
    (family : Finset (Row → ℕ)) (rows : Finset Row) : Prop :=
  ∀ f ∈ family, ∀ g ∈ family, f ≠ g → ∃ row ∈ rows,
    f row + 2 ≤ g row ∨ g row + 2 ≤ f row

/-- The fiber of a function class at a fixed row and value. -/
def coordinateFiber
    {Row : Type*} [DecidableEq Row]
    (family : Finset (Row → ℕ)) (row : Row) (level : ℕ) :
    Finset (Row → ℕ) :=
  family.filter fun f ↦ f row = level

@[simp] theorem mem_coordinateFiber
    {Row : Type*} [DecidableEq Row]
    {family : Finset (Row → ℕ)} {row : Row} {level : ℕ} {f : Row → ℕ} :
    f ∈ coordinateFiber family row level ↔ f ∈ family ∧ f row = level := by
  simp [coordinateFiber]

/-- Evaluation with the finite class itself used as the parameter type. -/
def finiteClassEvaluation
    {Row : Type*} (family : Finset (Row → ℕ)) :
    Row → ↥family → ℕ :=
  fun row f ↦ f.1 row

/-- Restricting to one coordinate fiber preserves pairwise two-separation on
the active rows after that coordinate is erased. -/
theorem IsPairwiseTwoSeparatedOn.coordinateFiber_erase
    {Row : Type*} [DecidableEq Row]
    {family : Finset (Row → ℕ)} {rows : Finset Row}
    (hseparated : IsPairwiseTwoSeparatedOn family rows)
    (row : Row) (level : ℕ) :
    IsPairwiseTwoSeparatedOn (coordinateFiber family row level)
      (rows.erase row) := by
  intro f hf g hg hfg
  have hf' := (mem_coordinateFiber.mp hf)
  have hg' := (mem_coordinateFiber.mp hg)
  obtain ⟨witnessRow, hwitnessRows, hwitnessGap⟩ :=
    hseparated f hf'.1 g hg'.1 hfg
  have hwitnessNe : witnessRow ≠ row := by
    intro heq
    subst witnessRow
    rw [hf'.2, hg'.2] at hwitnessGap
    omega
  exact ⟨witnessRow, Finset.mem_erase.mpr ⟨hwitnessNe, hwitnessRows⟩,
    hwitnessGap⟩

/-- Strong shattering is preserved when every parameter in a smaller class is
mapped into a larger class without changing evaluations. -/
theorem StronglyShattersAtUnit.reparam
    {Row SmallParameter LargeParameter : Type*} [DecidableEq Row]
    {smallValue : Row → SmallParameter → ℕ}
    {largeValue : Row → LargeParameter → ℕ}
    {rows : Finset Row} {threshold : Row → ℕ}
    (hshatters : StronglyShattersAtUnit smallValue rows threshold)
    (parameterMap : SmallParameter → LargeParameter)
    (hvalue : ∀ row parameter,
      largeValue row (parameterMap parameter) = smallValue row parameter) :
    StronglyShattersAtUnit largeValue rows threshold := by
  intro S hS
  obtain ⟨parameter, hhigh, hlow⟩ := hshatters S hS
  refine ⟨parameterMap parameter, ?_, ?_⟩
  · intro row hrow
    rw [hvalue]
    exact hhigh row hrow
  · intro row hrowRows hrowS
    rw [hvalue]
    exact hlow row hrowRows hrowS

/-- The inclusion of a coordinate fiber into its original finite class. -/
def coordinateFiberInclusion
    {Row : Type*} [DecidableEq Row]
    (family : Finset (Row → ℕ)) (row : Row) (level : ℕ) :
    ↥(coordinateFiber family row level) → ↥family :=
  fun f ↦ ⟨f.1, (mem_coordinateFiber.mp f.2).1⟩

/-- Common strong shattering in two coordinate fibers separated by two levels
raises the realized pair dimension in the original class. -/
theorem StronglyShattersAtUnit.insert_of_coordinateFibers
    {Row : Type*} [DecidableEq Row]
    {family : Finset (Row → ℕ)}
    {rows : Finset Row} {threshold : Row → ℕ}
    {newRow : Row} {lowLevel highLevel : ℕ}
    (hlowShatters : StronglyShattersAtUnit
      (finiteClassEvaluation (coordinateFiber family newRow lowLevel))
      rows threshold)
    (hhighShatters : StronglyShattersAtUnit
      (finiteClassEvaluation (coordinateFiber family newRow highLevel))
      rows threshold)
    (hlevels : lowLevel + 2 ≤ highLevel) :
    StronglyShattersAtUnit (finiteClassEvaluation family)
      (insert newRow rows) (Function.update threshold newRow (lowLevel + 1)) := by
  let LowFiber := ↥(coordinateFiber family newRow lowLevel)
  let HighFiber := ↥(coordinateFiber family newRow highLevel)
  have hsum : StronglyShattersAtUnit
      (sumEvaluation
        (finiteClassEvaluation (coordinateFiber family newRow lowLevel))
        (finiteClassEvaluation (coordinateFiber family newRow highLevel)))
      (insert newRow rows) (Function.update threshold newRow (lowLevel + 1)) := by
    apply StronglyShattersAtUnit.insert_of_sum hlowShatters hhighShatters
    · intro parameter
      exact (mem_coordinateFiber.mp parameter.2).2
    · intro parameter
      exact (mem_coordinateFiber.mp parameter.2).2
    · exact hlevels
  let parameterMap : LowFiber ⊕ HighFiber → ↥family :=
    Sum.elim
      (coordinateFiberInclusion family newRow lowLevel)
      (coordinateFiberInclusion family newRow highLevel)
  apply hsum.reparam parameterMap
  intro row parameter
  rcases parameter with parameter | parameter <;> rfl

end NormFormula
