import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Module.HahnBanach
import NormFormula.Analytic.IteratedLimits

/-!
# The compactness boundary in the local-stability proof

This file isolates the exact functional-analytic input as
`WeakSequentialCompactnessOnBounded` and formalizes all remaining subsequence
bookkeeping from the paper.  The later module `XWeakCompactness` discharges
this input for the paper's concrete space `XSpace` via its separable Hilbert
model and sequential Banach--Alaoglu.

In particular, after a weakly convergent subsequence is supplied, Lean refines
it so that the norms of the differences converge, proves that existing
successive scalar limits survive both subsequences, and combines these facts
with the verified Pythagorean calculation to show that the two iterated norm
limits agree.
-/

namespace NormFormula

noncomputable section

open Filter
open scoped Topology

/-- A scalar function of two natural-number variables has a successive limit
in the order “second variable first, then first variable”. -/
def HasSuccessiveLimit (F : ℕ → ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ inner : ℕ → ℝ,
    (∀ m, Tendsto (fun n ↦ F m n) atTop (𝓝 (inner m))) ∧
      Tendsto inner atTop (𝓝 a)

/-- Successive limits are unchanged after passing to subsequences in either
variable. -/
theorem HasSuccessiveLimit.subseq {F : ℕ → ℕ → ℝ} {a : ℝ}
    (h : HasSuccessiveLimit F a) {φ ψ : ℕ → ℕ}
    (hφ : StrictMono φ) (hψ : StrictMono ψ) :
    HasSuccessiveLimit (fun m n ↦ F (φ m) (ψ n)) a := by
  obtain ⟨inner, hInner, hOuter⟩ := h
  refine ⟨inner ∘ φ, ?_, ?_⟩
  · intro m
    simpa [Function.comp_def] using
      (hInner (φ m)).comp hψ.tendsto_atTop
  · exact hOuter.comp hφ.tendsto_atTop

/-- A successive limit, when it exists, is unique. -/
theorem HasSuccessiveLimit.unique {F : ℕ → ℕ → ℝ} {a b : ℝ}
    (ha : HasSuccessiveLimit F a) (hb : HasSuccessiveLimit F b) : a = b := by
  obtain ⟨innerA, hInnerA, hOuterA⟩ := ha
  obtain ⟨innerB, hInnerB, hOuterB⟩ := hb
  have hInner : innerA = innerB := by
    funext m
    exact tendsto_nhds_unique (hInnerA m) (hInnerB m)
  rw [hInner] at hOuterA
  exact tendsto_nhds_unique hOuterA hOuterB

/-- The exact weak sequential compactness property used by the manuscript:
every norm-bounded sequence has a weakly convergent subsequence. -/
def WeakSequentialCompactnessOnBounded
    (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z] : Prop :=
  ∀ (z : ℕ → Z) (C : ℝ), (∀ n, ‖z n‖ ≤ C) →
    ∃ x : Z, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ WeaklyTendsto (z ∘ φ) atTop x

/-- Weak convergence is preserved by precomposition with any map tending to
infinity. -/
theorem WeaklyTendsto.comp_tendsto
    {α β E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {z : α → E} {lα : Filter α} {lβ : Filter β} {x : E}
    (hz : WeaklyTendsto z lα x) {φ : β → α} (hφ : Tendsto φ lβ lα) :
    WeaklyTendsto (z ∘ φ) lβ x := by
  unfold WeaklyTendsto at hz ⊢
  exact hz.comp hφ

/-- A weak limit of a sequence contained in a closed norm ball remains in the
same ball.  The proof evaluates at a norming functional supplied by
Hahn--Banach and passes the scalar inequality to the limit. -/
theorem WeaklyTendsto.norm_le_of_forall_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {z : ℕ → E} {x : E} {C : ℝ}
    (hzWeak : WeaklyTendsto z atTop x)
    (hzBounded : ∀ n, ‖z n‖ ≤ C) :
    ‖x‖ ≤ C := by
  obtain ⟨g, hgNorm, hgx⟩ := exists_dual_vector'' ℝ x
  have hgWeak : WeaklyTendsto (fun n ↦ g (z n)) atTop (g x) :=
    hzWeak.map g
  have hgTendsto : Tendsto (fun n ↦ g (z n)) atTop (nhds (g x)) :=
    hgWeak.tendsto_of_finiteDimensional
  have hgBounded : ∀ n, g (z n) ≤ C := by
    intro n
    calc
      g (z n) ≤ ‖g (z n)‖ := by
        simpa only [Real.norm_eq_abs] using le_abs_self (g (z n))
      _ ≤ ‖g‖ * ‖z n‖ := g.le_opNorm (z n)
      _ ≤ 1 * C :=
        mul_le_mul hgNorm (hzBounded n) (norm_nonneg _) (by positivity)
      _ = C := one_mul C
  have hlimit : g x ≤ C :=
    le_of_tendsto hgTendsto (Eventually.of_forall hgBounded)
  simpa only [hgx] using hlimit

/-- Once a weakly convergent subsequence has been extracted, a further real
Bolzano–Weierstrass refinement makes the norms of its differences from the
weak limit converge. -/
theorem WeakSequentialCompactnessOnBounded.exists_prepared_subsequence
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (hcompact : WeakSequentialCompactnessOnBounded Z)
    (z : ℕ → Z) (C : ℝ) (hz : ∀ n, ‖z n‖ ≤ C) :
    ∃ x : Z, ∃ φ : ℕ → ℕ, ∃ limit : ℝ,
      StrictMono φ ∧ WeaklyTendsto (z ∘ φ) atTop x ∧
      Tendsto (fun n ↦ ‖z (φ n) - x‖) atTop (𝓝 limit) ∧
      ∀ n, ‖z (φ n) - x‖ ≤ C + ‖x‖ := by
  obtain ⟨x, φ, hφ, hφWeak⟩ := hcompact z C hz
  have hdiff (n : ℕ) : ‖z (φ n) - x‖ ≤ C + ‖x‖ := by
    calc
      ‖z (φ n) - x‖ ≤ ‖z (φ n)‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ C + ‖x‖ := add_le_add (hz (φ n)) le_rfl
  have hmem (n : ℕ) : ‖z (φ n) - x‖ ∈ Set.Icc 0 (C + ‖x‖) :=
    ⟨norm_nonneg _, hdiff n⟩
  obtain ⟨limit, _, ψ, hψ, hψNorm⟩ := isCompact_Icc.tendsto_subseq hmem
  refine ⟨x, φ ∘ ψ, limit, hφ.comp hψ, ?_, ?_, ?_⟩
  · simpa [Function.comp_def, Function.comp_assoc] using
      hφWeak.comp_tendsto hψ.tendsto_atTop
  · simpa [Function.comp_def] using hψNorm
  · intro n
    exact hdiff (ψ n)

/-- Ball-valued version of `exists_prepared_subsequence`: the weak limit is
packaged in the same closed norm ball as the original sequence. -/
theorem WeakSequentialCompactnessOnBounded.exists_prepared_subsequence_in_ball
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (hcompact : WeakSequentialCompactnessOnBounded Z)
    (z : ℕ → Z) (C : ℝ) (hz : ∀ n, ‖z n‖ ≤ C) :
    ∃ x : {x : Z // ‖x‖ ≤ C}, ∃ φ : ℕ → ℕ, ∃ limit : ℝ,
      StrictMono φ ∧ WeaklyTendsto (z ∘ φ) atTop x.1 ∧
      Tendsto (fun n ↦ ‖z (φ n) - x.1‖) atTop (nhds limit) ∧
      ∀ n, ‖z (φ n) - x.1‖ ≤ C + ‖x.1‖ := by
  obtain ⟨x, φ, limit, hφ, hxWeak, hxNorm, hxBound⟩ :=
    hcompact.exists_prepared_subsequence z C hz
  have hxBall : ‖x‖ ≤ C :=
    hxWeak.norm_le_of_forall_norm_le (fun n ↦ hz (φ n))
  exact ⟨⟨x, hxBall⟩, φ, limit, hφ, hxWeak, hxNorm, hxBound⟩

section L2Sum

variable {E : ℕ → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
variable [∀ i, FiniteDimensional ℝ (E i)]

/-- Conditional only on the explicitly isolated weak compactness input, the
two scalar iterated limits of the norm kernel on a dependent `ℓ₂`-sum agree.
Every analytic and subsequence step after compactness is discharged here. -/
theorem iterated_norm_limits_eq_of_weakSequentialCompactness
    (hcompact : WeakSequentialCompactnessOnBounded (lp E 2))
    {xSeq ySeq : ℕ → lp E 2} {Cx Cy firstLimit secondLimit : ℝ}
    (hxBounded : ∀ m, ‖xSeq m‖ ≤ Cx)
    (hyBounded : ∀ n, ‖ySeq n‖ ≤ Cy)
    (hFirst : HasSuccessiveLimit (fun m n ↦ ‖xSeq m + ySeq n‖) firstLimit)
    (hSecond : HasSuccessiveLimit (fun n m ↦ ‖xSeq m + ySeq n‖) secondLimit) :
    firstLimit = secondLimit := by
  obtain ⟨x, φ, xLimit, hφ, hxWeak, hxNorm, hxDiffBound⟩ :=
    hcompact.exists_prepared_subsequence xSeq Cx hxBounded
  obtain ⟨y, ψ, yLimit, hψ, hyWeak, hyNorm, hyDiffBound⟩ :=
    hcompact.exists_prepared_subsequence ySeq Cy hyBounded
  obtain ⟨hInnerFirst, hOuterFirst, hInnerSecond, hOuterSecond⟩ :=
    iterated_norm_limits_of_weaklyTendsto
      hxWeak hyWeak hxDiffBound hyDiffBound hxNorm hyNorm
  let common := pythagoreanDoubleLimit x y xLimit yLimit
  have hAnalyticFirst : HasSuccessiveLimit
      (fun m n ↦ ‖xSeq (φ m) + ySeq (ψ n)‖) common :=
    ⟨fun m ↦ Real.sqrt (‖xSeq (φ m) + y‖ ^ 2 + yLimit ^ 2),
      hInnerFirst, hOuterFirst⟩
  have hInheritedFirst := hFirst.subseq hφ hψ
  have hFirstEq : firstLimit = common :=
    hInheritedFirst.unique hAnalyticFirst
  have hAnalyticSecond : HasSuccessiveLimit
      (fun n m ↦ ‖xSeq (φ m) + ySeq (ψ n)‖) common :=
    ⟨fun n ↦ Real.sqrt (‖x + ySeq (ψ n)‖ ^ 2 + xLimit ^ 2),
      hInnerSecond, hOuterSecond⟩
  have hInheritedSecond := hSecond.subseq hψ hφ
  have hSecondEq : secondLimit = common :=
    hInheritedSecond.unique hAnalyticSecond
  exact hFirstEq.trans hSecondEq.symm

end L2Sum

namespace X

/-- The paper's double-limit conclusion for `XSpace`, conditional only on the
weak sequential compactness of bounded subsets of `XSpace`. -/
theorem iterated_norm_limits_eq_of_weakSequentialCompactness
    (hcompact : WeakSequentialCompactnessOnBounded XSpace)
    {xSeq ySeq : ℕ → XSpace} {Cx Cy firstLimit secondLimit : ℝ}
    (hxBounded : ∀ m, ‖xSeq m‖ ≤ Cx)
    (hyBounded : ∀ n, ‖ySeq n‖ ≤ Cy)
    (hFirst : HasSuccessiveLimit (fun m n ↦ ‖xSeq m + ySeq n‖) firstLimit)
    (hSecond : HasSuccessiveLimit (fun n m ↦ ‖xSeq m + ySeq n‖) secondLimit) :
    firstLimit = secondLimit :=
  NormFormula.iterated_norm_limits_eq_of_weakSequentialCompactness
    hcompact hxBounded hyBounded hFirst hSecond

end X

end

end NormFormula
