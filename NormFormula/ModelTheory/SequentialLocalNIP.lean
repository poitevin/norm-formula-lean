import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Topology.Sequences
import NormFormula.ModelTheory.ConnectiveClosure

/-!
# The sequential criterion for NIP on a distinguished model

For a separable structure in a countable language, the
Bourgain--Fremlin--Talagrand criterion says that a formula is NIP on the
distinguished model exactly when every sequence of its row functions has a
pointwise convergent subsequence on the corresponding local type space.

This file gives the pointwise sequential property a syntax-free definition,
proves its closure under binary ℓ₂-products, and isolates the BFT
identification with model-theoretic NIP in an explicit semantic interface.
The property here is deliberately different from `IsBoundedLocalNIP`, which
uniformly forbids finite IP patterns and therefore corresponds to the
stronger complete-theory behavior used elsewhere in this development.
-/

namespace NormFormula

noncomputable section

open Filter
open scoped Topology ENNReal

/-- Every bounded sequence of rows has a subsequence whose associated
functions converge pointwise on the chosen local parameter space. -/
def HasPointwiseConvergentSubsequenceOnBounded
    {X P : Type*} [Norm X] (value : X → P → ℝ) : Prop :=
  ∀ (rows : ℕ → X) (C : ℝ),
    (∀ n, ‖rows n‖ ≤ C) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ p : P, ∃ limit : ℝ,
          Tendsto (fun n ↦ value (rows (φ n)) p) atTop (𝓝 limit)

/-- The pointwise sequential property is preserved by an ℓ₂-product.

The parameter space `P` may be a saturated extension of the home product;
`toPE` and `toPF` are its named coordinate maps. The sole compatibility
assumption is the ℓ₂ norm identity for the three interpretations. -/
theorem hasPointwiseConvergentSubsequenceOnBounded_l2Sum
    {E F PE PF P : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    (eValue : E → PE → ℝ) (fValue : F → PF → ℝ)
    (sumValue : WithLp 2 (E × F) → P → ℝ)
    (toPE : P → PE) (toPF : P → PF)
    (hsum : ∀ z p,
      sumValue z p = euclideanConnective
        (eValue z.fst (toPE p)) (fValue z.snd (toPF p)))
    (he : HasPointwiseConvergentSubsequenceOnBounded eValue)
    (hf : HasPointwiseConvergentSubsequenceOnBounded fValue) :
    HasPointwiseConvergentSubsequenceOnBounded sumValue := by
  intro rows C hrows
  obtain ⟨φ, hφ, heConverges⟩ := he (fun n ↦ (rows n).fst) C fun n ↦
    (WithLp.norm_fst_le E (rows n)).trans (hrows n)
  obtain ⟨ψ, hψ, hfConverges⟩ := hf (fun n ↦ (rows (φ n)).snd) C fun n ↦
    (WithLp.norm_snd_le E (rows (φ n))).trans (hrows (φ n))
  refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
  intro p
  obtain ⟨eLimit, heLimit⟩ := heConverges (toPE p)
  obtain ⟨fLimit, hfLimit⟩ := hfConverges (toPF p)
  refine ⟨euclideanConnective eLimit fLimit, ?_⟩
  have heLimit' : Tendsto
      (fun n ↦ eValue (rows ((φ ∘ ψ) n)).fst (toPE p))
      atTop (𝓝 eLimit) := by
    simpa [Function.comp_def] using heLimit.comp hψ.tendsto_atTop
  have hpair : Tendsto
      (fun n ↦
        (eValue (rows ((φ ∘ ψ) n)).fst (toPE p),
          fValue (rows ((φ ∘ ψ) n)).snd (toPF p)))
      atTop (𝓝 (eLimit, fLimit)) := by
    exact heLimit'.prodMk_nhds (by simpa [Function.comp_def] using hfLimit)
  have hconnective :=
    euclideanConnective_uniformContinuous.continuous.continuousAt.tendsto.comp hpair
  simpa only [hsum] using hconnective

universe u v w

/-- An explicit interface for the BFT sequential characterization of NIP on
one distinguished model. The local parameter type may be implemented by a
local type space or by a sufficiently saturated elementary extension. -/
structure SequentialLocalNIPSemantics
    (X : Type u) [Norm X] where
  Parameter : Type v
  Formula : Type w
  formulaValue : Formula → X → Parameter → ℝ
  IsNIPOnDistinguished : Formula → Prop
  nip_iff_pointwiseSequential : ∀ φ,
    IsNIPOnDistinguished φ ↔
      HasPointwiseConvergentSubsequenceOnBounded (formulaValue φ)

namespace SequentialLocalNIPSemantics

/-- The semantic sequential criterion and the proved analytic product theorem
give closure of NIP on the distinguished model under binary ℓ₂-sums. -/
theorem l2Sum_isNIPOnDistinguished
    {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    (SE : SequentialLocalNIPSemantics E)
    (SF : SequentialLocalNIPSemantics F)
    (SS : SequentialLocalNIPSemantics (WithLp 2 (E × F)))
    (eFormula : SE.Formula) (fFormula : SF.Formula)
    (sumFormula : SS.Formula)
    (toPE : SS.Parameter → SE.Parameter)
    (toPF : SS.Parameter → SF.Parameter)
    (hsum : ∀ z p,
      SS.formulaValue sumFormula z p = euclideanConnective
        (SE.formulaValue eFormula z.fst (toPE p))
        (SF.formulaValue fFormula z.snd (toPF p)))
    (he : SE.IsNIPOnDistinguished eFormula)
    (hf : SF.IsNIPOnDistinguished fFormula) :
    SS.IsNIPOnDistinguished sumFormula := by
  rw [SS.nip_iff_pointwiseSequential]
  exact hasPointwiseConvergentSubsequenceOnBounded_l2Sum
    (SE.formulaValue eFormula) (SF.formulaValue fFormula)
    (SS.formulaValue sumFormula) toPE toPF hsum
    ((SE.nip_iff_pointwiseSequential eFormula).mp he)
    ((SF.nip_iff_pointwiseSequential fFormula).mp hf)

end SequentialLocalNIPSemantics

end

end NormFormula
