import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import NormFormula.Analytic.L2SumPythagoras
import NormFormula.Analytic.XSpace

/-!
# Weak convergence in dependent `ℓ₂`-sums

This file supplies the topological bridge in the paper's asymptotic
Pythagoras lemma.  It defines weak convergence using Mathlib's native
`WeakSpace`, proves functoriality under continuous linear maps, and proves
that weak convergence agrees with norm convergence on finite-dimensional real
normed spaces.  Coordinate projections then turn a weakly null sequence in a
dependent `ℓ₂`-sum of finite-dimensional spaces into the coordinatewise-null
sequence required by `L2SumPythagoras`.
-/

namespace NormFormula

noncomputable section

open Filter
open scoped Topology

/-- Convergence in the weak topology of a real normed space. -/
def WeaklyTendsto {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : α → E) (l : Filter α) (x : E) : Prop :=
  Tendsto (fun a ↦ toWeakSpace ℝ E (z a)) l (𝓝 (toWeakSpace ℝ E x))

/-- A weakly null sequence. -/
def IsWeaklyNull {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : ℕ → E) : Prop :=
  WeaklyTendsto z atTop 0

/-- Continuous linear maps preserve weak convergence. -/
theorem WeaklyTendsto.map
    {α E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {z : α → E} {l : Filter α} {x : E} (h : WeaklyTendsto z l x)
    (g : E →L[ℝ] F) : WeaklyTendsto (fun a ↦ g (z a)) l (g x) := by
  have hg := (WeakSpace.map g).continuous.continuousAt.tendsto.comp h
  simpa [WeaklyTendsto, WeakSpace.map_apply] using hg

/-- On a finite-dimensional real normed space, weak convergence implies norm
convergence.  The proof takes limits of all coordinates in a finite basis and
then reconstructs the vectors by the basis expansion. -/
theorem WeaklyTendsto.tendsto_of_finiteDimensional
    {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {z : α → E} {l : Filter α} {x : E}
    (h : WeaklyTendsto z l x) : Tendsto z l (𝓝 x) := by
  let b := Module.finBasis ℝ E
  have hcoord (i : Fin (Module.finrank ℝ E)) :
      Tendsto (fun a ↦ b.coord i (z a)) l (𝓝 (b.coord i x)) := by
    let c : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord i)
    have hc : Continuous (fun y : WeakSpace ℝ E ↦ c y) :=
      WeakBilin.eval_continuous (topDualPairing ℝ E).flip c
    have ht := hc.continuousAt.tendsto.comp h
    simpa [WeaklyTendsto, c] using ht
  have hsum := tendsto_finset_sum Finset.univ fun i _ ↦
    (hcoord i).smul_const (b i)
  simpa only [Module.Basis.coord_apply, Module.Basis.sum_repr] using hsum

section L2Sum

variable {ι : Type*} {E : ι → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

/-- The `i`th coordinate projection from a dependent `ℓ₂`-sum, bundled as a
continuous linear map. -/
def lpCoordCLM (i : ι) : lp E 2 →L[ℝ] E i where
  toFun f := f i
  map_add' f g := by
    change (f + g) i = f i + g i
    rw [lp.coeFn_add]
    rfl
  map_smul' c f := by
    change (c • f) i = c • f i
    rw [lp.coeFn_smul]
    rfl
  cont := (continuous_apply i).comp lp.uniformContinuous_coe.continuous

@[simp]
theorem lpCoordCLM_apply (i : ι) (f : lp E 2) : lpCoordCLM i f = f i :=
  rfl

/-- Weak convergence in the sum passes to weak convergence in every
coordinate. -/
theorem WeaklyTendsto.lpCoord {α : Type*} {z : α → lp E 2}
    {l : Filter α} {x : lp E 2} (h : WeaklyTendsto z l x) (i : ι) :
    WeaklyTendsto (fun a ↦ z a i) l (x i) := by
  simpa using h.map (lpCoordCLM i)

variable [∀ i, FiniteDimensional ℝ (E i)]

/-- In finite-dimensional summands, weak convergence in the sum gives norm
convergence of each coordinate. -/
theorem WeaklyTendsto.tendsto_lpCoord {α : Type*} {z : α → lp E 2}
    {l : Filter α} {x : lp E 2} (h : WeaklyTendsto z l x) (i : ι) :
    Tendsto (fun a ↦ z a i) l (𝓝 (x i)) :=
  (h.lpCoord i).tendsto_of_finiteDimensional

/-- A weakly null sequence in a dependent `ℓ₂`-sum of finite-dimensional
spaces is norm-null in every coordinate. -/
theorem IsWeaklyNull.tendsto_norm_apply {z : ℕ → lp E 2}
    (h : IsWeaklyNull z) (i : ι) :
    Tendsto (fun m ↦ ‖z m i‖) atTop (𝓝 0) := by
  have hi : Tendsto (fun m ↦ z m i) atTop (𝓝 0) := by
    simpa [IsWeaklyNull] using
      (show WeaklyTendsto z atTop (0 : lp E 2) from h).tendsto_lpCoord i
  simpa using hi.norm

variable [DecidableEq ι]

/-- The full asymptotic Pythagoras lemma from the paper: a bounded weakly null
sequence in an `ℓ₂`-sum of finite-dimensional spaces has the asserted squared
norm limit whenever its norms converge. -/
theorem tendsto_norm_add_sq_of_weaklyNull
    (u : lp E 2) {z : ℕ → lp E 2} {C limit : ℝ}
    (hzWeak : IsWeaklyNull z) (hzBounded : ∀ m, ‖z m‖ ≤ C)
    (hzNorm : Tendsto (fun m ↦ ‖z m‖) atTop (𝓝 limit)) :
    Tendsto (fun m ↦ ‖u + z m‖ ^ 2) atTop (𝓝 (‖u‖ ^ 2 + limit ^ 2)) :=
  tendsto_norm_add_sq_of_coordinatewise u hzBounded hzWeak.tendsto_norm_apply hzNorm

end L2Sum

namespace X

/-- Asymptotic Pythagoras specialized to the paper's renormed block sum
`XSpace`. -/
theorem tendsto_norm_add_sq_of_weaklyNull
    (u : XSpace) {z : ℕ → XSpace} {C limit : ℝ}
    (hzWeak : IsWeaklyNull z) (hzBounded : ∀ m, ‖z m‖ ≤ C)
    (hzNorm : Tendsto (fun m ↦ ‖z m‖) atTop (𝓝 limit)) :
    Tendsto (fun m ↦ ‖u + z m‖ ^ 2) atTop (𝓝 (‖u‖ ^ 2 + limit ^ 2)) :=
  NormFormula.tendsto_norm_add_sq_of_weaklyNull u hzWeak hzBounded hzNorm

end X

end

end NormFormula
