import NormFormula.Analytic.CompactnessBoundary

/-!
# Stability on bounded Banach-space sorts

Continuous Banach logic treats variables as belonging to fixed norm-ball
sorts.  Accordingly, the manuscript's double-limit definition of stability
can be expressed without a syntax library as a property of a real-valued
binary function on every pair of norm-bounded sequences.
-/

namespace NormFormula

/-- The double-limit condition for a real kernel on two fixed sorts. -/
def IsStableKernel {X Y : Type*} (value : X → Y → ℝ) : Prop :=
  ∀ (xs : ℕ → X) (ys : ℕ → Y) (a b : ℝ),
    HasSuccessiveLimit (fun m n ↦ value (xs m) (ys n)) a →
    HasSuccessiveLimit (fun n m ↦ value (xs m) (ys n)) b → a = b

/-- A real-valued binary function is stable on bounded sets when its two
successive limits agree for every pair of norm-bounded sequences whenever
both limits exist.

This is the concrete double-limit property corresponding to stability on all
fixed ball sorts of a Banach structure. -/
def IsStableOnBounded {X Y : Type*} [Norm X] [Norm Y]
    (value : X → Y → ℝ) : Prop :=
  ∀ (xSeq : ℕ → X) (ySeq : ℕ → Y) (Cx Cy firstLimit secondLimit : ℝ),
    (∀ m, ‖xSeq m‖ ≤ Cx) →
    (∀ n, ‖ySeq n‖ ≤ Cy) →
    HasSuccessiveLimit (fun m n ↦ value (xSeq m) (ySeq n)) firstLimit →
    HasSuccessiveLimit (fun n m ↦ value (xSeq m) (ySeq n)) secondLimit →
    firstLimit = secondLimit


/-- Pulling a stable function back along norm-nonincreasing maps preserves
stability on bounded sets. -/
theorem IsStableOnBounded.comap
    {X Y X' Y' : Type*} [Norm X] [Norm Y] [Norm X'] [Norm Y']
    {value : X → Y → ℝ} (hstable : IsStableOnBounded value)
    (mapX : X' → X) (mapY : Y' → Y)
    (hmapX : ∀ x, ‖mapX x‖ ≤ ‖x‖)
    (hmapY : ∀ y, ‖mapY y‖ ≤ ‖y‖) :
    IsStableOnBounded fun x y ↦ value (mapX x) (mapY y) := by
  intro xSeq ySeq Cx Cy firstLimit secondLimit hxBounded hyBounded hFirst hSecond
  exact hstable (fun m ↦ mapX (xSeq m)) (fun n ↦ mapY (ySeq n))
    Cx Cy firstLimit secondLimit
    (fun m ↦ (hmapX (xSeq m)).trans (hxBounded m))
    (fun n ↦ (hmapY (ySeq n)).trans (hyBounded n))
    hFirst hSecond

/-- Bounded interpretations and a nonzero normalization preserve stability
on fixed sorts, which need not themselves carry norms. -/
theorem IsStableOnBounded.normalized_comap
    {X Y A B : Type*} [Norm X] [Norm Y] {value : X → Y → ℝ}
    (hstable : IsStableOnBounded value) (r : A → X) (p : B → Y)
    (R S c : ℝ) (hc : c ≠ 0)
    (hr : ∀ x, ‖r x‖ ≤ R) (hp : ∀ y, ‖p y‖ ≤ S) :
    IsStableKernel (fun x y ↦ value (r x) (p y) / c) := by
  intro xs ys a b ha hb
  have scale {F : ℕ → ℕ → ℝ} {a : ℝ}
      (h : HasSuccessiveLimit (fun m n ↦ F m n / c) a) :
      HasSuccessiveLimit F (a * c) := by
    obtain ⟨inner, hinner, houter⟩ := h
    refine ⟨fun m ↦ inner m * c, ?_, houter.mul_const c⟩
    intro m
    simpa only [div_mul_cancel₀ _ hc] using (hinner m).mul_const c
  exact mul_right_cancel₀ hc
    (hstable (r ∘ xs) (p ∘ ys) R S (a*c) (b*c)
      (fun m ↦ hr _) (fun n ↦ hp _) (scale ha) (scale hb))

end NormFormula
