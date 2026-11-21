import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.UnitInterval
import NormFormula.ContinuousLogic.RationalConnectiveCode

/-!
# Density of rational lattice connectives

Rational lattice codes are uniformly dense in the continuous real-valued
functions on every finite truth-value cube.  The proof uses the lattice form
of Stone--Weierstrass.  Rational coefficients are handled first by passing to
the closure of the code interpretations; that closure contains all real
constant and one-coordinate affine functions, hence separates points
strongly.

Clamping is a contraction, so the real-valued approximation immediately
gives uniform approximation of bounded continuous connectives.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open scoped Topology

namespace RationalLatticeCode

/-- The real interpretations of rational lattice codes at a fixed arity. -/
def realCodeRange (arity : ℕ) :
    Set C((Fin arity → TruthValue), ℝ) :=
  Set.range (realContinuousMap : RationalLatticeCode arity →
    C((Fin arity → TruthValue), ℝ))

/-- Rational code interpretations are closed under pointwise minimum. -/
theorem min_mem_realCodeRange {arity : ℕ}
    {first second : C((Fin arity → TruthValue), ℝ)}
    (hfirst : first ∈ realCodeRange arity)
    (hsecond : second ∈ realCodeRange arity) :
    first ⊓ second ∈ realCodeRange arity := by
  obtain ⟨firstCode, rfl⟩ := hfirst
  obtain ⟨secondCode, rfl⟩ := hsecond
  refine ⟨.min firstCode secondCode, ?_⟩
  ext values
  rfl

/-- Rational code interpretations are closed under pointwise maximum. -/
theorem max_mem_realCodeRange {arity : ℕ}
    {first second : C((Fin arity → TruthValue), ℝ)}
    (hfirst : first ∈ realCodeRange arity)
    (hsecond : second ∈ realCodeRange arity) :
    first ⊔ second ∈ realCodeRange arity := by
  obtain ⟨firstCode, rfl⟩ := hfirst
  obtain ⟨secondCode, rfl⟩ := hsecond
  refine ⟨.max firstCode secondCode, ?_⟩
  ext values
  rfl

/-- Pointwise minimum is Lipschitz on pairs of continuous real-valued maps
with the uniform metric. -/
theorem lipschitzWith_continuousMap_inf {arity : ℕ} :
    LipschitzWith 1
      (fun pair : C((Fin arity → TruthValue), ℝ) ×
          C((Fin arity → TruthValue), ℝ) => pair.1 ⊓ pair.2) := by
  apply LipschitzWith.mk_one
  intro first second
  rw [ContinuousMap.dist_le_iff_of_nonempty]
  intro values
  rw [Real.dist_eq, Prod.dist_eq]
  exact (abs_min_sub_min_le_max
    (first.1 values) (first.2 values)
    (second.1 values) (second.2 values)).trans
      (max_le_max
        (by simpa [Real.dist_eq] using
          (ContinuousMap.dist_apply_le_dist
            (f := first.1) (g := second.1) values))
        (by simpa [Real.dist_eq] using
          (ContinuousMap.dist_apply_le_dist
            (f := first.2) (g := second.2) values)))

/-- Pointwise maximum is Lipschitz on pairs of continuous real-valued maps
with the uniform metric. -/
theorem lipschitzWith_continuousMap_sup {arity : ℕ} :
    LipschitzWith 1
      (fun pair : C((Fin arity → TruthValue), ℝ) ×
          C((Fin arity → TruthValue), ℝ) => pair.1 ⊔ pair.2) := by
  apply LipschitzWith.mk_one
  intro first second
  rw [ContinuousMap.dist_le_iff_of_nonempty]
  intro values
  rw [Real.dist_eq, Prod.dist_eq]
  exact (abs_max_sub_max_le_max
    (first.1 values) (first.2 values)
    (second.1 values) (second.2 values)).trans
      (max_le_max
        (by simpa [Real.dist_eq] using
          (ContinuousMap.dist_apply_le_dist
            (f := first.1) (g := second.1) values))
        (by simpa [Real.dist_eq] using
          (ContinuousMap.dist_apply_le_dist
            (f := first.2) (g := second.2) values)))

/-- The closure of the rational code interpretations remains closed under
pointwise minimum. -/
theorem min_mem_closure_realCodeRange {arity : ℕ}
    {first second : C((Fin arity → TruthValue), ℝ)}
    (hfirst : first ∈ closure (realCodeRange arity))
    (hsecond : second ∈ closure (realCodeRange arity)) :
    first ⊓ second ∈ closure (realCodeRange arity) := by
  refine map_mem_closure₂ (f := fun f g => f ⊓ g) ?_ hfirst hsecond ?_
  · exact lipschitzWith_continuousMap_inf.continuous
  · intro f hf g hg
    exact min_mem_realCodeRange hf hg

/-- The closure of the rational code interpretations remains closed under
pointwise maximum. -/
theorem max_mem_closure_realCodeRange {arity : ℕ}
    {first second : C((Fin arity → TruthValue), ℝ)}
    (hfirst : first ∈ closure (realCodeRange arity))
    (hsecond : second ∈ closure (realCodeRange arity)) :
    first ⊔ second ∈ closure (realCodeRange arity) := by
  refine map_mem_closure₂ (f := fun f g => f ⊔ g) ?_ hfirst hsecond ?_
  · exact lipschitzWith_continuousMap_sup.continuous
  · intro f hf g hg
    exact max_mem_realCodeRange hf hg

/-- A real constant, bundled as a continuous function on a truth-value cube. -/
def realConstantMap (arity : ℕ) (value : ℝ) :
    C((Fin arity → TruthValue), ℝ) :=
  value • (1 : C((Fin arity → TruthValue), ℝ))

/-- The family of real constant maps depends continuously on its value. -/
theorem continuous_realConstantMap (arity : ℕ) :
    Continuous (realConstantMap arity) :=
  continuous_id.smul continuous_const

/-- Every real constant map lies in the closure of the rational code
interpretations. -/
theorem realConstantMap_mem_closure_realCodeRange (arity : ℕ) (value : ℝ) :
    realConstantMap arity value ∈ closure (realCodeRange arity) := by
  have hmem : realConstantMap arity value ∈
      closure (realConstantMap arity '' Set.range ((↑) : ℚ → ℝ)) :=
    (continuous_realConstantMap arity).range_subset_closure_image_dense
      Rat.denseRange_cast ⟨value, rfl⟩
  refine closure_mono ?_ hmem
  rintro function ⟨_, ⟨rational, rfl⟩, rfl⟩
  refine ⟨.constant rational, ?_⟩
  ext values
  simp [realConstantMap, realContinuousMap, realValue]

/-- The real coordinate projection on a finite truth-value cube. -/
def realCoordinateMap {arity : ℕ} (coordinate : Fin arity) :
    C((Fin arity → TruthValue), ℝ) :=
  ⟨fun values => (values coordinate : ℝ),
    continuous_subtype_val.comp (continuous_apply coordinate)⟩

/-- A real affine function of one coordinate, bundled as a continuous map. -/
def realAffineMap {arity : ℕ} (coordinate : Fin arity)
    (coefficients : ℝ × ℝ) : C((Fin arity → TruthValue), ℝ) :=
  coefficients.1 • (1 : C((Fin arity → TruthValue), ℝ)) +
    coefficients.2 • realCoordinateMap coordinate

/-- The one-coordinate affine map depends continuously on its two
coefficients. -/
theorem continuous_realAffineMap {arity : ℕ} (coordinate : Fin arity) :
    Continuous (realAffineMap coordinate) :=
  (continuous_fst.smul continuous_const).add
    (continuous_snd.smul continuous_const)

/-- Every real one-coordinate affine function lies in the closure of the
rational code interpretations. -/
theorem realAffineMap_mem_closure_realCodeRange {arity : ℕ}
    (coordinate : Fin arity) (coefficients : ℝ × ℝ) :
    realAffineMap coordinate coefficients ∈
      closure (realCodeRange arity) := by
  let rationalPair : ℚ × ℚ → ℝ × ℝ :=
    Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)
  have rationalPair_dense : DenseRange rationalPair :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hmem : realAffineMap coordinate coefficients ∈
      closure (realAffineMap coordinate '' Set.range rationalPair) :=
    (continuous_realAffineMap coordinate).range_subset_closure_image_dense
      rationalPair_dense ⟨coefficients, rfl⟩
  refine closure_mono ?_ hmem
  rintro function ⟨_, ⟨rational, rfl⟩, rfl⟩
  refine ⟨.affine coordinate rational.1 rational.2, ?_⟩
  ext values
  simp [realAffineMap, realCoordinateMap, realContinuousMap, realValue,
    rationalPair]

/-- The closure of the rational code interpretations strongly separates
points of the finite truth-value cube. -/
theorem closure_realCodeRange_separatesPointsStrongly (arity : ℕ) :
    (closure (realCodeRange arity)).SeparatesPointsStrongly := by
  intro values first second
  by_cases hsame : first = second
  · subst second
    refine ⟨realConstantMap arity (values first),
      realConstantMap_mem_closure_realCodeRange arity (values first), ?_, ?_⟩
    · simp [realConstantMap]
    · simp [realConstantMap]
  · have hcoordinate : ∃ coordinate, first coordinate ≠ second coordinate := by
      by_contra h
      push Not at h
      exact hsame (funext h)
    obtain ⟨coordinate, hcoordinate⟩ := hcoordinate
    have hdenominator :
        (second coordinate : ℝ) - (first coordinate : ℝ) ≠ 0 :=
      sub_ne_zero.mpr (Subtype.coe_injective.ne hcoordinate.symm)
    let slope : ℝ :=
      (values second - values first) /
        ((second coordinate : ℝ) - (first coordinate : ℝ))
    let bias : ℝ := values first - slope * (first coordinate : ℝ)
    refine ⟨realAffineMap coordinate (bias, slope),
      realAffineMap_mem_closure_realCodeRange coordinate (bias, slope), ?_, ?_⟩
    · simp [realAffineMap, realCoordinateMap, bias]
    · simp only [realAffineMap, realCoordinateMap, ContinuousMap.add_apply,
        ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul,
        mul_one]
      change bias + slope * (second coordinate : ℝ) = values second
      dsimp [bias, slope]
      field_simp [hdenominator]
      ring

/-- Rational lattice codes are dense among all real-valued continuous
functions on a finite truth-value cube. -/
theorem closure_realCodeRange_eq_top (arity : ℕ) :
    closure (realCodeRange arity) =
      (Set.univ : Set C((Fin arity → TruthValue), ℝ)) := by
  let lattice := closure (realCodeRange arity)
  have lattice_nonempty : lattice.Nonempty := by
    refine ⟨realContinuousMap (.constant 0), subset_closure ?_⟩
    exact ⟨.constant 0, rfl⟩
  have lattice_inf : ∀ᵉ (f ∈ lattice) (g ∈ lattice), f ⊓ g ∈ lattice := by
    intro f hf g hg
    exact min_mem_closure_realCodeRange hf hg
  have lattice_sup : ∀ᵉ (f ∈ lattice) (g ∈ lattice), f ⊔ g ∈ lattice := by
    intro f hf g hg
    exact max_mem_closure_realCodeRange hf hg
  have hdense := ContinuousMap.sublattice_closure_eq_top lattice
    lattice_nonempty lattice_inf lattice_sup
      (closure_realCodeRange_separatesPointsStrongly arity)
  simpa [lattice, isClosed_closure.closure_eq] using hdense

/-- The interpretations of rational lattice codes have dense range in the
space of all real-valued continuous functions on a finite truth-value cube. -/
theorem denseRange_realContinuousMap (arity : ℕ) :
    DenseRange (realContinuousMap : RationalLatticeCode arity →
      C((Fin arity → TruthValue), ℝ)) := by
  rw [DenseRange, dense_iff_closure_eq]
  exact closure_realCodeRange_eq_top arity

end RationalLatticeCode

/-- Clamping to `[0,1]` does not increase real distance. -/
theorem abs_clampTruthValue_sub_clampTruthValue_le (first second : ℝ) :
    |(clampTruthValue first : ℝ) - (clampTruthValue second : ℝ)| ≤
      |first - second| := by
  simpa [clampTruthValue, Set.projIcc] using
    (Set.abs_projIcc_sub_projIcc (a := (0 : ℝ)) (b := 1)
      zero_le_one (c := first) (d := second))

namespace Connective

/-- The real-valued continuous map underlying a bounded connective. -/
def realContinuousMap {arity : ℕ} (connective : Connective arity) :
    C((Fin arity → TruthValue), ℝ) :=
  ⟨fun values => (connective values : ℝ),
    continuous_subtype_val.comp connective.continuous_toFun⟩

/-- Every bounded continuous connective is uniformly approximated by a
rational lattice code. -/
theorem exists_rationalLatticeCode_uniformly_close {arity : ℕ}
    (connective : Connective arity) {ε : ℝ} (hε : 0 < ε) :
    ∃ code : RationalLatticeCode arity, ∀ values,
      |(code.toConnective values : ℝ) - (connective values : ℝ)| < ε := by
  obtain ⟨code, hcode⟩ :=
    (RationalLatticeCode.denseRange_realContinuousMap arity).exists_dist_lt
      connective.realContinuousMap hε
  refine ⟨code, fun values => ?_⟩
  have hpoint :
      |code.realValue values - (connective values : ℝ)| < ε := by
    have hpoint' :
        dist (connective.realContinuousMap values)
          (code.realContinuousMap values) < ε :=
      (ContinuousMap.dist_apply_le_dist values).trans_lt hcode
    simpa [realContinuousMap, RationalLatticeCode.realContinuousMap,
      Real.dist_eq, abs_sub_comm] using hpoint'
  have hfixed :
      (clampTruthValue (connective values : ℝ) : ℝ) =
        (connective values : ℝ) := by
    simp [clampTruthValue, (connective values).property.1,
      (connective values).property.2]
  change |(clampTruthValue (code.realValue values) : ℝ) -
    (connective values : ℝ)| < ε
  rw [← hfixed]
  exact (abs_clampTruthValue_sub_clampTruthValue_le
    (code.realValue values) (connective values : ℝ)).trans_lt hpoint

end Connective

end

end NormFormula.ContinuousLogic
