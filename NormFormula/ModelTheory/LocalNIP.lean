import NormFormula.Combinatorics.FiniteIPPattern

/-!
# Bounded local NIP via finite patterns

This module records the finite-pattern notion of NIP that can be stated
without a continuous-logic syntax.  A real-valued binary function has bounded
local NIP when, on every fixed pair of norm balls and at every fixed positive
gap, its finite IP patterns have uniformly bounded dimension.
-/

namespace NormFormula

/-- The closed norm ball used as a parameter sort. -/
abbrev ClosedNormBall (E : Type*) [Norm E] (R : ℝ) := {x : E // ‖x‖ ≤ R}

/-- Restrict a binary real-valued function to prescribed rows and a closed
parameter ball. -/
def boundedBinaryValue {X Y : Type*} [Norm Y]
    (value : X → Y → ℝ) {n : ℕ} (rows : Fin n → X) (R_y : ℝ) :
    Fin n → ClosedNormBall Y R_y → ℝ :=
  fun i y ↦ value (rows i) y.1

/-- Quantitative bounded local NIP: fixed row and parameter balls and a fixed
positive low/high gap admit a uniform upper bound on IP-pattern dimension. -/
def IsBoundedLocalNIP {X Y : Type*} [Norm X] [Norm Y]
    (value : X → Y → ℝ) : Prop :=
  ∀ R_x R_y low high : ℝ, low < high →
    ∃ N : ℕ, ∀ (n : ℕ) (rows : Fin n → X),
      (∀ i, ‖rows i‖ ≤ R_x) →
      IsIPPattern (boundedBinaryValue value rows R_y) low high → n < N

/-- Fixed bounded IP patterns occur in every finite dimension.  The negation
of this property is the qualitative consequence of bounded local NIP. -/
def HasIPPatternsInEveryDimension {X Y : Type*} [Norm X] [Norm Y]
    (value : X → Y → ℝ) (R_x R_y low high : ℝ) : Prop :=
  ∀ n : ℕ, ∃ rows : Fin n → X,
    (∀ i, ‖rows i‖ ≤ R_x) ∧
    IsIPPattern (boundedBinaryValue value rows R_y) low high

/-- The quantitative definition rules out fixed bounded IP patterns in all
finite dimensions. -/
theorem IsBoundedLocalNIP.not_hasIPPatternsInEveryDimension
    {X Y : Type*} [Norm X] [Norm Y] {value : X → Y → ℝ}
    (hlocal : IsBoundedLocalNIP value)
    {R_x R_y low high : ℝ} (hgap : low < high) :
    ¬ HasIPPatternsInEveryDimension value R_x R_y low high := by
  obtain ⟨N, hN⟩ := hlocal R_x R_y low high hgap
  intro hall
  obtain ⟨rows, hrows, hip⟩ := hall N
  exact (Nat.lt_irrefl N) (hN N rows hrows hip)

/-- Bounded local NIP is preserved by pulling both variables back along
norm-nonincreasing maps. -/
theorem IsBoundedLocalNIP.comap
    {X Y X' Y' : Type*} [Norm X] [Norm Y] [Norm X'] [Norm Y']
    {value : X → Y → ℝ} (hlocal : IsBoundedLocalNIP value)
    (mapX : X' → X) (mapY : Y' → Y)
    (hmapX : ∀ x, ‖mapX x‖ ≤ ‖x‖)
    (hmapY : ∀ y, ‖mapY y‖ ≤ ‖y‖) :
    IsBoundedLocalNIP fun x y ↦ value (mapX x) (mapY y) := by
  intro R_x R_y low high hgap
  obtain ⟨N, hN⟩ := hlocal R_x R_y low high hgap
  refine ⟨N, ?_⟩
  intro n rows hrows hip
  let mappedRows : Fin n → X := fun i ↦ mapX (rows i)
  have hmappedRows : ∀ i, ‖mappedRows i‖ ≤ R_x := by
    intro i
    exact (hmapX (rows i)).trans (hrows i)
  apply hN n mappedRows hmappedRows
  intro S
  obtain ⟨y, hin, hout⟩ := hip S
  let mappedY : ClosedNormBall Y R_y :=
    ⟨mapY y.1, (hmapY y.1).trans y.2⟩
  refine ⟨mappedY, ?_, ?_⟩
  · intro i hi
    exact hin i hi
  · intro i hi
    exact hout i hi

/-- A missing finite dimension at every fixed gap gives a uniform bound:
larger patterns restrict to that dimension. -/
theorem isBoundedLocalNIP_of_no_patterns
    {X Y : Type*} [Norm X] [Norm Y] (value : X → Y → ℝ)
    (h : ∀ R S low high : ℝ, low < high →
      ¬ HasIPPatternsInEveryDimension value R S low high) : IsBoundedLocalNIP value := by
  classical
  intro R S low high hgap
  have hn := h R S low high hgap
  unfold HasIPPatternsInEveryDimension at hn
  push Not at hn
  obtain ⟨N, hN⟩ := hn
  refine ⟨N, ?_⟩
  intro n rows hrows hp
  by_contra hlt
  have hle : N ≤ n := by omega
  let e : Fin N ↪ Fin n := ⟨Fin.castLE hle, Fin.castLE_injective _⟩
  apply hN (fun i ↦ rows (e i)) (fun i ↦ hrows (e i))
  intro A
  obtain ⟨y, hhi, hlo⟩ := hp (A.map e)
  refine ⟨y, ?_, ?_⟩
  · intro i hi
    exact hhi (e i) (Finset.mem_map.mpr ⟨i, hi, rfl⟩)
  · intro i hi
    exact hlo (e i) (by simpa using hi)

end NormFormula
