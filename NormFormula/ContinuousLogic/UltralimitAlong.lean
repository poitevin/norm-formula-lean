import NormFormula.ContinuousLogic.Ultralimit

/-!
# Truth-value ultralimits along an arbitrary ultrafilter

This is the index-polymorphic form of the sequential ultralimit API.  The
original `ultralimit` remains as the specialization to `indexUltrafilter` on
`ℕ`, so existing developments are unchanged.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Filter
open scoped Topology

universe κ

/-- The canonical limit of a truth-value family along an arbitrary
ultrafilter. -/
def ultralimitAlong {ι : Type κ} (U : Ultrafilter ι)
    (values : ι → TruthValue) : TruthValue :=
  (U.map values).lim

/-- Every truth-value family converges to its canonical ultralimit. -/
theorem tendsto_ultralimitAlong {ι : Type κ} (U : Ultrafilter ι)
    (values : ι → TruthValue) :
    Tendsto values U (𝓝 (ultralimitAlong U values)) := by
  rw [Tendsto, ← Ultrafilter.coe_map]
  exact (U.map values).le_nhds_lim

/-- The ultralimit is the unique limit along the ultrafilter. -/
theorem ultralimitAlong_eq_of_tendsto {ι : Type κ} {U : Ultrafilter ι}
    {values : ι → TruthValue} {limit : TruthValue}
    (hlimit : Tendsto values U (𝓝 limit)) :
    ultralimitAlong U values = limit :=
  tendsto_nhds_unique (tendsto_ultralimitAlong U values) hlimit


/-- The ultralimit of a constant family is constant. -/
@[simp]
theorem ultralimitAlong_const {ι : Type κ} (U : Ultrafilter ι)
    (c : TruthValue) :
    ultralimitAlong U (fun _ : ι ↦ c) = c :=
  ultralimitAlong_eq_of_tendsto tendsto_const_nhds


/-- An eventual real upper bound passes to an arbitrary-index ultralimit. -/
theorem ultralimitAlong_coe_le_of_eventually_le {ι : Type κ}
    (U : Ultrafilter ι) (values : ι → TruthValue) (c : ℝ)
    (h : ∀ᶠ i in U, (values i : ℝ) ≤ c) :
    (ultralimitAlong U values : ℝ) ≤ c := by
  apply isClosed_Iic.mem_of_tendsto
      (continuous_subtype_val.continuousAt.tendsto.comp
        (tendsto_ultralimitAlong U values))
  exact h

/-- An eventual real lower bound passes to an arbitrary-index ultralimit. -/
theorem le_ultralimitAlong_coe_of_eventually_le {ι : Type κ}
    (U : Ultrafilter ι) (values : ι → TruthValue) (c : ℝ)
    (h : ∀ᶠ i in U, c ≤ (values i : ℝ)) :
    c ≤ (ultralimitAlong U values : ℝ) := by
  apply isClosed_Ici.mem_of_tendsto
      (continuous_subtype_val.continuousAt.tendsto.comp
        (tendsto_ultralimitAlong U values))
  exact h

/-- Eventual pointwise order is preserved by arbitrary-index ultralimits. -/
theorem ultralimitAlong_mono {ι : Type κ} {U : Ultrafilter ι}
    {a b : ι → TruthValue} (h : ∀ᶠ i in U, a i ≤ b i) :
    ultralimitAlong U a ≤ ultralimitAlong U b := by
  have ha : Tendsto (fun i ↦ (a i : ℝ)) U
      (𝓝 (ultralimitAlong U a : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp
      (tendsto_ultralimitAlong U a)
  have hb : Tendsto (fun i ↦ (b i : ℝ)) U
      (𝓝 (ultralimitAlong U b : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp
      (tendsto_ultralimitAlong U b)
  exact (isClosed_le continuous_fst continuous_snd).mem_of_tendsto
    (ha.prodMk_nhds hb) h

/-- A vanishing real error can be removed after taking an ultralimit. -/
theorem ultralimitAlong_coe_le_of_eventually_le_add_tendsto_zero
    {ι : Type κ} (U : Ultrafilter ι) (a b : ι → TruthValue)
    (error : ι → ℝ) (herror : Tendsto error U (𝓝 0))
    (h : ∀ᶠ i in U, (a i : ℝ) ≤ (b i : ℝ) + error i) :
    ultralimitAlong U a ≤ ultralimitAlong U b := by
  have ha : Tendsto (fun i ↦ (a i : ℝ)) U
      (𝓝 (ultralimitAlong U a : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp
      (tendsto_ultralimitAlong U a)
  have hb : Tendsto (fun i ↦ (b i : ℝ)) U
      (𝓝 (ultralimitAlong U b : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp
      (tendsto_ultralimitAlong U b)
  have hle : (ultralimitAlong U a : ℝ) ≤
      (ultralimitAlong U b : ℝ) + 0 :=
    (isClosed_le continuous_fst continuous_snd).mem_of_tendsto
      (ha.prodMk_nhds (hb.add herror)) h
  simpa using hle

/-- The triangle-inequality form of passage to arbitrary-index
ultralimits. -/
theorem ultralimitAlong_coe_le_add_of_eventually_le
    {ι : Type κ} (U : Ultrafilter ι) (a b c : ι → TruthValue)
    (h : ∀ᶠ i in U,
      (a i : ℝ) ≤ (b i : ℝ) + (c i : ℝ)) :
    (ultralimitAlong U a : ℝ) ≤
      (ultralimitAlong U b : ℝ) + (ultralimitAlong U c : ℝ) := by
  have ha : Tendsto (fun i ↦ (a i : ℝ)) U
      (𝓝 (ultralimitAlong U a : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp
      (tendsto_ultralimitAlong U a)
  have hb : Tendsto (fun i ↦ (b i : ℝ)) U
      (𝓝 (ultralimitAlong U b : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp
      (tendsto_ultralimitAlong U b)
  have hc : Tendsto (fun i ↦ (c i : ℝ)) U
      (𝓝 (ultralimitAlong U c : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp
      (tendsto_ultralimitAlong U c)
  exact (isClosed_le continuous_fst continuous_snd).mem_of_tendsto
    (ha.prodMk_nhds (hb.add hc)) h

/-- Coordinatewise ultralimits give the limit of a finite tuple. -/
theorem tendsto_ultralimitAlong_pi {ι : Type κ} {arity : ℕ}
    (U : Ultrafilter ι) (values : Fin arity → ι → TruthValue) :
    Tendsto (fun i j ↦ values j i) U
      (𝓝 (fun j ↦ ultralimitAlong U (values j))) := by
  rw [tendsto_pi_nhds]
  intro j
  exact tendsto_ultralimitAlong U (values j)

/-- Arbitrary-index ultralimits commute with finitary continuous
connectives. -/
theorem ultralimitAlong_connective {ι : Type κ} {arity : ℕ}
    (U : Ultrafilter ι) (F : Connective arity)
    (values : Fin arity → ι → TruthValue) :
    ultralimitAlong U (fun i ↦ F (fun j ↦ values j i)) =
      F (fun j ↦ ultralimitAlong U (values j)) := by
  apply ultralimitAlong_eq_of_tendsto
  exact F.continuous_toFun.continuousAt.tendsto.comp
    (tendsto_ultralimitAlong_pi U values)

end

end NormFormula.ContinuousLogic
