import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Hausdorff
import NormFormula.ContinuousLogic.Basic

/-!
# Ultralimits of bounded truth values

This file supplies the compact-Hausdorff ultralimit engine for the future
metric ultraproduct.  We fix Mathlib's free ultrafilter on `ℕ`, define the
canonical ultralimit of every sequence in `[0,1]`, and prove the properties
needed in the connective step of Łoś's theorem.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Filter
open scoped Topology

/-- A fixed free ultrafilter on `ℕ`, extending the cofinite filter. -/
def indexUltrafilter : Ultrafilter ℕ :=
  Filter.hyperfilter ℕ

/-- The chosen ultrafilter contains every tail of `ℕ`. -/
theorem indexUltrafilter_le_atTop :
    (indexUltrafilter : Filter ℕ) ≤ atTop := by
  exact Nat.hyperfilter_le_atTop

/-- Every eventually-at-top property holds along the chosen ultrafilter. -/
theorem eventually_indexUltrafilter_of_eventually_atTop
    {p : ℕ → Prop} (hp : ∀ᶠ n in atTop, p n) :
    ∀ᶠ n in indexUltrafilter, p n :=
  indexUltrafilter_le_atTop hp

/-- In particular, every numerical tail belongs to the chosen ultrafilter. -/
theorem eventually_ge_indexUltrafilter (N : ℕ) :
    ∀ᶠ n in indexUltrafilter, N ≤ n :=
  eventually_indexUltrafilter_of_eventually_atTop (eventually_ge_atTop N)

/-- No finite set belongs to the chosen ultrafilter. -/
theorem finite_not_mem_indexUltrafilter {s : Set ℕ} (hs : s.Finite) :
    s ∉ indexUltrafilter := by
  exact hs.notMem_hyperfilter

/-- The canonical ultralimit of a bounded truth-value sequence.  Compactness
gives existence and Hausdorffness gives uniqueness. -/
def ultralimit (values : ℕ → TruthValue) : TruthValue :=
  (indexUltrafilter.map values).lim

/-- Every truth-value sequence converges to its canonical ultralimit along the
chosen ultrafilter. -/
theorem tendsto_ultralimit (values : ℕ → TruthValue) :
    Tendsto values indexUltrafilter (𝓝 (ultralimit values)) := by
  rw [Tendsto, ← Ultrafilter.coe_map]
  exact (indexUltrafilter.map values).le_nhds_lim

/-- The ultralimit is the unique limit along the chosen ultrafilter. -/
theorem ultralimit_eq_of_tendsto {values : ℕ → TruthValue} {limit : TruthValue}
    (hlimit : Tendsto values indexUltrafilter (𝓝 limit)) :
    ultralimit values = limit :=
  tendsto_nhds_unique (tendsto_ultralimit values) hlimit

/-- Changing a sequence on an ultrafilter-small set does not change its
ultralimit. -/
theorem ultralimit_congr {values values' : ℕ → TruthValue}
    (h : values =ᶠ[indexUltrafilter] values') :
    ultralimit values = ultralimit values' :=
  tendsto_nhds_unique_of_eventuallyEq
    (tendsto_ultralimit values) (tendsto_ultralimit values') h

/-- The ultralimit of a constant sequence is that constant. -/
@[simp]
theorem ultralimit_const (c : TruthValue) :
    ultralimit (fun _ : ℕ ↦ c) = c :=
  ultralimit_eq_of_tendsto tendsto_const_nhds

/-- Ultralimits commute with continuous unary maps of truth values. -/
theorem ultralimit_comp_continuous
    (F : TruthValue → TruthValue) (hF : Continuous F)
    (values : ℕ → TruthValue) :
    ultralimit (fun n ↦ F (values n)) = F (ultralimit values) := by
  apply ultralimit_eq_of_tendsto
  exact hF.continuousAt.tendsto.comp (tendsto_ultralimit values)

/-- An eventual real upper bound passes to the ultralimit. -/
theorem ultralimit_coe_le_of_eventually_le
    (values : ℕ → TruthValue) (c : ℝ)
    (h : ∀ᶠ n in indexUltrafilter, (values n : ℝ) ≤ c) :
    (ultralimit values : ℝ) ≤ c := by
  apply isClosed_Iic.mem_of_tendsto
      (continuous_subtype_val.continuousAt.tendsto.comp
        (tendsto_ultralimit values))
  exact h

/-- An eventual real lower bound passes to the ultralimit. -/
theorem le_ultralimit_coe_of_eventually_le
    (values : ℕ → TruthValue) (c : ℝ)
    (h : ∀ᶠ n in indexUltrafilter, c ≤ (values n : ℝ)) :
    c ≤ (ultralimit values : ℝ) := by
  apply isClosed_Ici.mem_of_tendsto
      (continuous_subtype_val.continuousAt.tendsto.comp
        (tendsto_ultralimit values))
  exact h

/-- Eventual pointwise order is preserved by truth-value ultralimits. -/
theorem ultralimit_mono {a b : ℕ → TruthValue}
    (h : ∀ᶠ n in indexUltrafilter, a n ≤ b n) :
    ultralimit a ≤ ultralimit b := by
  have ha : Tendsto (fun n ↦ (a n : ℝ)) indexUltrafilter
      (𝓝 (ultralimit a : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp (tendsto_ultralimit a)
  have hb : Tendsto (fun n ↦ (b n : ℝ)) indexUltrafilter
      (𝓝 (ultralimit b : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp (tendsto_ultralimit b)
  exact (isClosed_le continuous_fst continuous_snd).mem_of_tendsto
    (ha.prodMk_nhds hb) h

/-- An eventual inequality with a real error tending to zero passes to the
ultralimit with the error removed. -/
theorem ultralimit_coe_le_of_eventually_le_add_tendsto_zero
    (a b : ℕ → TruthValue) (error : ℕ → ℝ)
    (herror : Tendsto error indexUltrafilter (𝓝 0))
    (h : ∀ᶠ n in indexUltrafilter,
      (a n : ℝ) ≤ (b n : ℝ) + error n) :
    ultralimit a ≤ ultralimit b := by
  have ha : Tendsto (fun n ↦ (a n : ℝ)) indexUltrafilter
      (𝓝 (ultralimit a : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp (tendsto_ultralimit a)
  have hb : Tendsto (fun n ↦ (b n : ℝ)) indexUltrafilter
      (𝓝 (ultralimit b : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp (tendsto_ultralimit b)
  have hle : (ultralimit a : ℝ) ≤ (ultralimit b : ℝ) + 0 :=
    (isClosed_le continuous_fst continuous_snd).mem_of_tendsto
      (ha.prodMk_nhds (hb.add herror)) h
  simpa using hle

/-- An eventual inequality between one truth-value sequence and the sum of
two others passes to their ultralimits.  This is the form used to transport
the triangle inequality to the ultralimit pseudometric. -/
theorem ultralimit_coe_le_add_of_eventually_le
    (a b c : ℕ → TruthValue)
    (h : ∀ᶠ n in indexUltrafilter,
      (a n : ℝ) ≤ (b n : ℝ) + (c n : ℝ)) :
    (ultralimit a : ℝ) ≤ (ultralimit b : ℝ) + (ultralimit c : ℝ) := by
  have ha : Tendsto (fun n ↦ (a n : ℝ)) indexUltrafilter
      (𝓝 (ultralimit a : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp (tendsto_ultralimit a)
  have hb : Tendsto (fun n ↦ (b n : ℝ)) indexUltrafilter
      (𝓝 (ultralimit b : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp (tendsto_ultralimit b)
  have hc : Tendsto (fun n ↦ (c n : ℝ)) indexUltrafilter
      (𝓝 (ultralimit c : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp (tendsto_ultralimit c)
  exact (isClosed_le continuous_fst continuous_snd).mem_of_tendsto
    (ha.prodMk_nhds (hb.add hc)) h

/-- The tuple of coordinate sequences converges to the tuple of coordinate
ultralimits. -/
theorem tendsto_ultralimit_pi {arity : ℕ}
    (values : Fin arity → ℕ → TruthValue) :
    Tendsto (fun n i ↦ values i n) indexUltrafilter
      (𝓝 (fun i ↦ ultralimit (values i))) := by
  rw [tendsto_pi_nhds]
  intro i
  exact tendsto_ultralimit (values i)

/-- Ultralimits commute with every finitary continuous connective in the
minimal language.  This is the connective case of the future Łoś theorem. -/
theorem ultralimit_connective {arity : ℕ} (F : Connective arity)
    (values : Fin arity → ℕ → TruthValue) :
    ultralimit (fun n ↦ F (fun i ↦ values i n)) =
      F (fun i ↦ ultralimit (values i)) := by
  apply ultralimit_eq_of_tendsto
  exact F.continuous_toFun.continuousAt.tendsto.comp
    (tendsto_ultralimit_pi values)

end

end NormFormula.ContinuousLogic
