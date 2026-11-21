import Mathlib.Algebra.Order.Floor.Ring
import NormFormula.Combinatorics.MetricPacking

/-!
# Scale-sensitive discretization

This file formalizes the real-to-finite-range reduction in the
scale-sensitive Sauer lemma. Values are divided by a positive mesh and
rounded down. Strong unit shattering of the discretized class yields
fat-shattering of the original class at half the mesh, while separation by
twice the mesh survives as separation by two integer levels.
-/

namespace NormFormula

/-- Downward discretization of a nonnegative real value at mesh `ρ`. -/
noncomputable def floorDiscretization (ρ value : ℝ) : ℕ :=
  ⌊value / ρ⌋₊

/-- The discretized lower endpoint does not exceed the original value. -/
theorem floorDiscretization_mul_le
    {ρ value : ℝ} (hρ : 0 < ρ) (hvalue : 0 ≤ value) :
    ρ * floorDiscretization ρ value ≤ value := by
  have hfloor :
      ((floorDiscretization ρ value : ℕ) : ℝ) ≤ value / ρ := by
    exact Nat.floor_le (div_nonneg hvalue hρ.le)
  have := (le_div_iff₀ hρ).mp hfloor
  simpa [mul_comm] using this

/-- The original value lies strictly below the next discretization level. -/
theorem lt_floorDiscretization_succ_mul
    {ρ value : ℝ} (hρ : 0 < ρ) :
    value < ρ * (floorDiscretization ρ value + 1) := by
  have hfloor := Nat.lt_floor_add_one (value / ρ)
  have := (div_lt_iff₀ hρ).mp hfloor
  simpa [floorDiscretization, mul_comm, Nat.cast_add, Nat.cast_one] using this

/-- A real separation of two mesh widths produces a separation of at least
two integer levels after downward discretization. -/
theorem floorDiscretization_add_two_le_of_add_two_mul_le
    {ρ value other : ℝ} (hρ : 0 < ρ) (hvalue : 0 ≤ value)
    (hseparated : value + 2 * ρ ≤ other) :
    floorDiscretization ρ value + 2 ≤ floorDiscretization ρ other := by
  apply Nat.le_floor
  apply (le_div_iff₀ hρ).2
  have hlower := floorDiscretization_mul_le hρ hvalue
  push_cast
  nlinarith

/-- Unit strong shattering for a natural-valued evaluation class. The low
and high integer values lie at least one full level on opposite sides of the
row threshold. -/
def IsStronglyShatteredAtUnit
    {Row Parameter : Type*} [Fintype Row]
    (value : Row → Parameter → ℕ) : Prop :=
  ∃ threshold : Row → ℕ, ∀ S : Finset Row, ∃ parameter : Parameter,
    (∀ row ∈ S, threshold row + 1 ≤ value row parameter) ∧
    (∀ row ∉ S, value row parameter + 1 ≤ threshold row)

/-- Strong unit shattering of the downward discretization implies
fat-shattering of the original nonnegative class at margin `ρ/2`. -/
theorem isFatShattered_half_mesh_of_stronglyShattered_discretization
    {Row Parameter : Type*} [Fintype Row]
    {value : Row → Parameter → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (hvalue : ∀ row parameter, 0 ≤ value row parameter)
    (hstrong : IsStronglyShatteredAtUnit
      (fun row parameter ↦ floorDiscretization ρ (value row parameter))) :
    IsFatShattered value (ρ / 2) := by
  obtain ⟨discreteThreshold, hdiscrete⟩ := hstrong
  let threshold : Row → ℝ := fun row ↦
    ρ * discreteThreshold row + ρ / 2
  refine ⟨threshold, ?_⟩
  intro S
  obtain ⟨parameter, hhigh, hlow⟩ := hdiscrete S
  refine ⟨parameter, ?_, ?_⟩
  · intro row hrow
    have hcode := hhigh row hrow
    have hcodeReal :
        ((discreteThreshold row + 1 : ℕ) : ℝ) ≤
          floorDiscretization ρ (value row parameter) := by
      exact_mod_cast hcode
    have hlower := floorDiscretization_mul_le hρ (hvalue row parameter)
    dsimp [threshold]
    push_cast at hcodeReal
    nlinarith [mul_le_mul_of_nonneg_left hcodeReal hρ.le]
  · intro row hrow
    have hcode := hlow row hrow
    have hcodeReal :
        ((floorDiscretization ρ (value row parameter) + 1 : ℕ) : ℝ) ≤
          discreteThreshold row := by
      exact_mod_cast hcode
    have hupper := lt_floorDiscretization_succ_mul
      (ρ := ρ) (value := value row parameter) hρ
    dsimp [threshold]
    push_cast at hcodeReal
    nlinarith [mul_le_mul_of_nonneg_left hcodeReal hρ.le]

/-- Pairwise real separation by `2ρ` survives discretization as pairwise
separation by two natural levels in some row coordinate. -/
theorem floorDiscretization_coordinateSeparated
    {Row Parameter : Type*} [Fintype Row]
    {value : Row → Parameter → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (hvalue : ∀ row parameter, 0 ≤ value row parameter)
    (hseparated : ∀ p q, p ≠ q → ∃ row,
      2 * ρ ≤ |value row p - value row q|) :
    ∀ p q, p ≠ q → ∃ row,
      floorDiscretization ρ (value row p) + 2 ≤
          floorDiscretization ρ (value row q) ∨
        floorDiscretization ρ (value row q) + 2 ≤
          floorDiscretization ρ (value row p) := by
  intro p q hpq
  obtain ⟨row, hrow⟩ := hseparated p q hpq
  refine ⟨row, ?_⟩
  rcases (le_abs.mp hrow) with hrow | hrow
  · right
    apply floorDiscretization_add_two_le_of_add_two_mul_le
      hρ (hvalue row q)
    linarith
  · left
    apply floorDiscretization_add_two_le_of_add_two_mul_le
      hρ (hvalue row p)
    linarith

/-- A uniform upper bound on the original values gives a finite upper bound
on all discretized values. -/
theorem floorDiscretization_le_of_le
    {ρ value bound : ℝ} (hρ : 0 < ρ) (hbound : value ≤ bound) :
    floorDiscretization ρ value ≤ floorDiscretization ρ bound := by
  exact Nat.floor_le_floor (div_le_div_of_nonneg_right hbound hρ.le)

end NormFormula
