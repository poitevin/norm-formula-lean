import NormFormula.Analytic.YPredicates
import NormFormula.ContinuousLogic.AbsoluteDifference
import NormFormula.ContinuousLogic.ElementaryDiagram
import NormFormula.ContinuousLogic.ElementaryDiagramCompactness
import NormFormula.ContinuousLogic.EuclideanConnective
import NormFormula.ContinuousLogic.MultiPredicate
import NormFormula.ContinuousLogic.MultiTheoryIP
import NormFormula.ContinuousLogic.NormAdd
import NormFormula.ContinuousLogic.SequentialElementaryDiagram

/-!
# The bounded expanded language for `Y`

On each positive norm ball, the expansion names three normalized translation
predicates: the ambient norm, the underlying Hilbert norm, and `q`.  The
one-symbol norm language maps into this expansion, and its structure is the
corresponding reduct.  The general map/reduct theorem therefore supplies
evaluation preservation for every formula, including quantified formulae.
-/

namespace NormFormula.HalfGraph.Y.ContinuousLanguage

noncomputable section

open scoped Topology
open NormFormula.ContinuousLogic

universe u v

/-- The sole predicate symbol of the Banach reduct. -/
inductive ReductSymbol
  | norm
  deriving DecidableEq

/-- The three named predicates of the expansion used in the proof for `Y`. -/
inductive ExpansionSymbol
  | norm
  | hilbert
  | q
  deriving DecidableEq

/-- Inclusion of the norm language into the three-predicate expansion. -/
def includeReduct : ReductSymbol → ExpansionSymbol
  | .norm => .norm

/-- Normalized Hilbert-norm translation on a positive `Y`-ball. -/
def hilbertAddTruth (R : ℝ) (hR : 0 < R)
    (x y : PositiveNormBall Y R) : TruthValue := by
  refine ⟨hilbertNormPredicate (x.1 + y.1) / (2 * R),
    div_nonneg (hilbertNormPredicate_nonneg _) (by positivity), ?_⟩
  apply (div_le_one (by positivity : 0 < 2 * R)).2
  exact (hilbertNormPredicate_le_norm (x.1 + y.1)).trans <|
    (norm_add_le x.1 y.1).trans (add_le_add x.2 y.2) |>.trans_eq (by ring)

/-- Normalized `q` translation on a positive `Y`-ball. -/
def qAddTruth (R : ℝ) (hR : 0 < R)
    (x y : PositiveNormBall Y R) : TruthValue := by
  refine ⟨qPredicate (x.1 + y.1) / (2 * R),
    div_nonneg (qPredicate_nonneg _) (by positivity), ?_⟩
  apply (div_le_one (by positivity : 0 < 2 * R)).2
  exact (qPredicate_le_norm (x.1 + y.1)).trans <|
    (norm_add_le x.1 y.1).trans (add_le_add x.2 y.2) |>.trans_eq (by ring)

@[simp]
theorem hilbertAddTruth_coe (R : ℝ) (hR : 0 < R)
    (x y : PositiveNormBall Y R) :
    (hilbertAddTruth R hR x y : ℝ) =
      hilbertNormPredicate (x.1 + y.1) / (2 * R) :=
  rfl

@[simp]
theorem qAddTruth_coe (R : ℝ) (hR : 0 < R)
    (x y : PositiveNormBall Y R) :
    (qAddTruth R hR x y : ℝ) = qPredicate (x.1 + y.1) / (2 * R) :=
  rfl

/-- Uniform continuity of normalized Hilbert-norm addition. -/
theorem hilbertAddTruth_uniformContinuous (R : ℝ) (hR : 0 < R) :
    UniformContinuous fun p : PositiveNormBall Y R × PositiveNormBall Y R ↦
      hilbertAddTruth R hR p.1 p.2 := by
  have hfst : UniformContinuous
      (fun p : PositiveNormBall Y R × PositiveNormBall Y R ↦ (p.1.1 : Y)) :=
    uniformContinuous_subtype_val.comp uniformContinuous_fst
  have hsnd : UniformContinuous
      (fun p : PositiveNormBall Y R × PositiveNormBall Y R ↦ (p.2.1 : Y)) :=
    uniformContinuous_subtype_val.comp uniformContinuous_snd
  have hpredicate : UniformContinuous
      (fun p : PositiveNormBall Y R × PositiveNormBall Y R ↦
        hilbertNormPredicate ((p.1.1 : Y) + (p.2.1 : Y))) :=
    hilbertNormPredicate_uniformContinuous.comp (hfst.add hsnd)
  exact (hpredicate.div_const' (2 * R)).subtype_mk _

/-- Uniform continuity of normalized `q` addition. -/
theorem qAddTruth_uniformContinuous (R : ℝ) (hR : 0 < R) :
    UniformContinuous fun p : PositiveNormBall Y R × PositiveNormBall Y R ↦
      qAddTruth R hR p.1 p.2 := by
  have hfst : UniformContinuous
      (fun p : PositiveNormBall Y R × PositiveNormBall Y R ↦ (p.1.1 : Y)) :=
    uniformContinuous_subtype_val.comp uniformContinuous_fst
  have hsnd : UniformContinuous
      (fun p : PositiveNormBall Y R × PositiveNormBall Y R ↦ (p.2.1 : Y)) :=
    uniformContinuous_subtype_val.comp uniformContinuous_snd
  have hpredicate : UniformContinuous
      (fun p : PositiveNormBall Y R × PositiveNormBall Y R ↦
        qPredicate ((p.1.1 : Y) + (p.2.1 : Y))) :=
    qPredicate_uniformContinuous.comp (hfst.add hsnd)
  exact (hpredicate.div_const' (2 * R)).subtype_mk _

/-- The three-predicate bounded expansion on the positive `R`-ball of `Y`. -/
def expansionStructure (R : ℝ) (hR : 0 < R) :
    MultiStructure ExpansionSymbol where
  Row := PositiveNormBall Y R
  Parameter := PositiveNormBall Y R
  rowNonempty := ⟨⟨0, by simpa using hR.le⟩⟩
  parameterNonempty := ⟨⟨0, by simpa using hR.le⟩⟩
  predicate
    | .norm => normAddTruth R hR
    | .hilbert => hilbertAddTruth R hR
    | .q => qAddTruth R hR
  predicate_uniformContinuous := by
    intro symbol
    cases symbol with
    | norm => exact normAddTruth_uniformContinuous R hR
    | hilbert => exact hilbertAddTruth_uniformContinuous R hR
    | q => exact qAddTruth_uniformContinuous R hR

/-- Both sorts of the expanded positive `Y`-ball have diameter at most
`2R`. -/
def expansionStructureBounds (R : ℝ) (hR : 0 < R) :
    (expansionStructure R hR).Bounds where
  row := (normAddStructureBounds (E := Y) R hR).row
  parameter := (normAddStructureBounds (E := Y) R hR).parameter

/-- The bounded norm-language structure is definitionally the reduct of the
three-predicate expansion. -/
def reductStructure (R : ℝ) (hR : 0 < R) :
    MultiStructure ReductSymbol :=
  (expansionStructure R hR).reduct includeReduct

/-- The atomic norm formula of the reduct language. -/
def normFormula : MultiFormula ReductSymbol 1 1 :=
  .predicate .norm 0 0

/-- The atomic Hilbert predicate of the expansion. -/
def hilbertFormula : MultiFormula ExpansionSymbol 1 1 :=
  .predicate .hilbert 0 0

/-- The atomic `q` predicate of the expansion. -/
def qFormula : MultiFormula ExpansionSymbol 1 1 :=
  .predicate .q 0 0

/-- The bounded Euclidean combination of the named Hilbert and `q`
predicates. -/
def reconstructionFormula : MultiFormula ExpansionSymbol 1 1 :=
  .connective boundedEuclideanConnective ![hilbertFormula, qFormula]

/-- Pointwise absolute discrepancy between the lifted norm formula and its
Hilbert--`q` reconstruction. -/
def reconstructionDiscrepancyFormula : MultiFormula ExpansionSymbol 1 1 :=
  .connective absoluteDifferenceConnective
    ![normFormula.map includeReduct, reconstructionFormula]

/-- The worst-case reconstruction discrepancy, expressed as a sentence of
the expanded language. -/
def reconstructionDiscrepancySentence : MultiSentence ExpansionSymbol :=
  .iSupParameter (.iSupRow reconstructionDiscrepancyFormula)

/-- Every reduct formula has the same value after it is lifted into the
expansion. -/
theorem realize_liftReduct {rowVars parameterVars : ℕ}
    (R : ℝ) (hR : 0 < R)
    (φ : MultiFormula ReductSymbol rowVars parameterVars)
    (rows : Fin rowVars → PositiveNormBall Y R)
    (parameters : Fin parameterVars → PositiveNormBall Y R) :
    (φ.map includeReduct).realize (expansionStructure R hR) rows parameters =
      φ.realize (reductStructure R hR) rows parameters :=
  MultiFormula.realize_map_reduct includeReduct (expansionStructure R hR)
    φ rows parameters

@[simp]
theorem normFormula_value (R : ℝ) (hR : 0 < R)
    (x y : PositiveNormBall Y R) :
    normFormula.binaryValue (reductStructure R hR) x y =
      ‖x.1 + y.1‖ / (2 * R) :=
  rfl

@[simp]
theorem hilbertFormula_value (R : ℝ) (hR : 0 < R)
    (x y : PositiveNormBall Y R) :
    hilbertFormula.binaryValue (expansionStructure R hR) x y =
      hilbertNormPredicate (x.1 + y.1) / (2 * R) :=
  rfl

@[simp]
theorem qFormula_value (R : ℝ) (hR : 0 < R)
    (x y : PositiveNormBall Y R) :
    qFormula.binaryValue (expansionStructure R hR) x y =
      qPredicate (x.1 + y.1) / (2 * R) :=
  rfl

/-- Scaling both named predicates by `2R` commutes with their Euclidean
combination.  The result is the normalized ambient norm. -/
theorem normalized_euclidean_eq_norm (R : ℝ) (hR : 0 < R)
    (x y : PositiveNormBall Y R) :
    NormFormula.euclideanConnective
        (hilbertNormPredicate (x.1 + y.1) / (2 * R))
        (qPredicate (x.1 + y.1) / (2 * R)) =
      ‖x.1 + y.1‖ / (2 * R) := by
  have hdenom : 0 < 2 * R := by positivity
  have hsum : 0 ≤
      hilbertNormPredicate (x.1 + y.1) ^ 2 +
        qPredicate (x.1 + y.1) ^ 2 := by positivity
  rw [NormFormula.euclideanConnective]
  have hradicand :
      (hilbertNormPredicate (x.1 + y.1) / (2 * R)) ^ 2 +
          (qPredicate (x.1 + y.1) / (2 * R)) ^ 2 =
        (hilbertNormPredicate (x.1 + y.1) ^ 2 +
          qPredicate (x.1 + y.1) ^ 2) / (2 * R) ^ 2 := by
    field_simp [ne_of_gt hdenom]
  rw [hradicand, Real.sqrt_div hsum, Real.sqrt_sq hdenom.le,
    ← norm_eq_sqrt_predicates]

/-- On every positive `Y`-ball, the reconstruction formula has exactly the
normalized ambient-norm value.  In particular, clipping at `1` is inactive. -/
@[simp]
theorem reconstructionFormula_value (R : ℝ) (hR : 0 < R)
    (x y : PositiveNormBall Y R) :
    reconstructionFormula.binaryValue (expansionStructure R hR) x y =
      ‖x.1 + y.1‖ / (2 * R) := by
  change min 1
      (NormFormula.euclideanConnective
        (hilbertNormPredicate (x.1 + y.1) / (2 * R))
        (qPredicate (x.1 + y.1) / (2 * R))) = _
  rw [normalized_euclidean_eq_norm R hR]
  exact min_eq_right (normAddTruth R hR x y).2.2

/-- The lifted reduct norm formula and the reconstruction formula agree at
every pair of elements in the expanded positive ball. -/
theorem reconstructionFormula_eq_liftedNormFormula
    (R : ℝ) (hR : 0 < R) (x y : PositiveNormBall Y R) :
    reconstructionFormula.binaryValue (expansionStructure R hR) x y =
      (normFormula.map includeReduct).binaryValue
        (expansionStructure R hR) x y := by
  rw [reconstructionFormula_value]
  rfl

/-- Equality of the two formula realizations as bounded truth values, for
arbitrary assignments of their one row and one parameter variable. -/
theorem reconstructionFormula_realize_eq_liftedNormFormula
    (R : ℝ) (hR : 0 < R)
    (rows : Fin 1 → PositiveNormBall Y R)
    (parameters : Fin 1 → PositiveNormBall Y R) :
    reconstructionFormula.realize (expansionStructure R hR) rows parameters =
      (normFormula.map includeReduct).realize
        (expansionStructure R hR) rows parameters := by
  apply Subtype.ext
  exact reconstructionFormula_eq_liftedNormFormula
    R hR (rows 0) (parameters 0)

/-- In the distinguished `Y`-expansion, every pointwise reconstruction
discrepancy is zero. -/
@[simp]
theorem reconstructionDiscrepancyFormula_realize
    (R : ℝ) (hR : 0 < R)
    (rows : Fin 1 → PositiveNormBall Y R)
    (parameters : Fin 1 → PositiveNormBall Y R) :
    reconstructionDiscrepancyFormula.realize
        (expansionStructure R hR) rows parameters = zeroTruthValue := by
  apply Subtype.ext
  change |(((normFormula.map includeReduct).realize
      (expansionStructure R hR) rows parameters : TruthValue) : ℝ) -
    ((reconstructionFormula.realize
      (expansionStructure R hR) rows parameters : TruthValue) : ℝ)| = 0
  rw [reconstructionFormula_realize_eq_liftedNormFormula]
  simp

/-- The quantified reconstruction-discrepancy sentence has value zero in the
distinguished `Y`-expansion. -/
@[simp]
theorem reconstructionDiscrepancySentence_value
    (R : ℝ) (hR : 0 < R) :
    reconstructionDiscrepancySentence.value (expansionStructure R hR) =
      zeroTruthValue := by
  change (⨆ parameter : PositiveNormBall Y R,
      ⨆ row : PositiveNormBall Y R,
        reconstructionDiscrepancyFormula.realize
          (expansionStructure R hR)
          (Fin.cons row Fin.elim0) (Fin.cons parameter Fin.elim0)) =
    zeroTruthValue
  apply le_antisymm
  · refine iSup_le fun parameter ↦ iSup_le fun row ↦ ?_
    exact (reconstructionDiscrepancyFormula_realize R hR
      (Fin.cons row Fin.elim0) (Fin.cons parameter Fin.elim0)).le
  · exact ((⨆ parameter : PositiveNormBall Y R,
      ⨆ row : PositiveNormBall Y R,
        reconstructionDiscrepancyFormula.realize
          (expansionStructure R hR)
          (Fin.cons row Fin.elim0) (Fin.cons parameter Fin.elim0)) :
      TruthValue).2.1

/-- Every pointwise discrepancy is bounded above by the value of the
universally quantified discrepancy sentence. -/
theorem reconstructionDiscrepancyFormula_le_sentenceValue
    (N : MultiStructure.{u, v} ExpansionSymbol)
    (rows : Fin 1 → N.Row) (parameters : Fin 1 → N.Parameter) :
    reconstructionDiscrepancyFormula.realize N rows parameters ≤
      reconstructionDiscrepancySentence.value N := by
  have hrows : rows = Fin.cons (rows 0) Fin.elim0 := by
    funext i
    fin_cases i
    rfl
  have hparameters : parameters = Fin.cons (parameters 0) Fin.elim0 := by
    funext i
    fin_cases i
    rfl
  rw [hrows, hparameters]
  refine le_iSup_of_le (parameters 0) ?_
  exact le_iSup
    (fun row : N.Row ↦ reconstructionDiscrepancyFormula.realize N
      (Fin.cons row Fin.elim0) (Fin.cons (parameters 0) Fin.elim0))
    (rows 0)

/-- Equality of complete expanded theories transfers the reconstruction
identity to every model: the discrepancy sentence remains zero, hence so does
each of its pointwise instances. -/
theorem reconstructionFormula_equivalent_of_sameCompleteTheory
    (R : ℝ) (hR : 0 < R)
    (N : MultiStructure.{u, v} ExpansionSymbol)
    (hTheory : MultiSameCompleteTheory (expansionStructure R hR) N)
    (rows : Fin 1 → N.Row) (parameters : Fin 1 → N.Parameter) :
    (normFormula.map includeReduct).realize N rows parameters =
      reconstructionFormula.realize N rows parameters := by
  have hsentence : reconstructionDiscrepancySentence.value N =
      zeroTruthValue := by
    calc
      reconstructionDiscrepancySentence.value N =
          reconstructionDiscrepancySentence.value (expansionStructure R hR) :=
        (hTheory reconstructionDiscrepancySentence).symm
      _ = zeroTruthValue := reconstructionDiscrepancySentence_value R hR
  have hle := reconstructionDiscrepancyFormula_le_sentenceValue N rows parameters
  rw [hsentence] at hle
  have hzero : reconstructionDiscrepancyFormula.realize N rows parameters =
      zeroTruthValue := by
    apply le_antisymm hle
    exact (reconstructionDiscrepancyFormula.realize N rows parameters).2.1
  apply Subtype.ext
  have hcoe := congrArg (fun value : TruthValue ↦ (value : ℝ)) hzero
  change |(((normFormula.map includeReduct).realize N rows parameters :
      TruthValue) : ℝ) -
    ((reconstructionFormula.realize N rows parameters : TruthValue) : ℝ)| = 0
    at hcoe
  exact sub_eq_zero.mp (abs_eq_zero.mp hcoe)

/-- Packaged complete-theory equivalence of the lifted norm formula and the
Hilbert--`q` reconstruction formula. -/
theorem reconstructionFormula_equivalentInCompleteTheory
    (R : ℝ) (hR : 0 < R) :
    MultiFormula.EquivalentInCompleteTheory (expansionStructure R hR)
      (normFormula.map includeReduct) reconstructionFormula := by
  intro N hTheory rows parameters
  exact reconstructionFormula_equivalent_of_sameCompleteTheory
    R hR N hTheory rows parameters

/-- Concrete use of equivalence invariance: NIP of the Hilbert--`q`
reconstruction formula implies NIP of the lifted norm formula in the complete
expanded theory. -/
theorem liftedNormFormula_isNIP_of_reconstructionFormula_isNIP
    (R : ℝ) (hR : 0 < R)
    (hreconstruction : MultiFormula.IsNIPInCompleteTheory
      (expansionStructure R hR) reconstructionFormula) :
    MultiFormula.IsNIPInCompleteTheory (expansionStructure R hR)
      (normFormula.map includeReduct) :=
  MultiFormula.nip_of_equivalent
    (reconstructionFormula_equivalentInCompleteTheory R hR) hreconstruction

/-- Every finite constant-enriched diagram fragment of a model of the complete
norm reduct theory is approximately realized in the distinguished expanded
`Y`-ball.  This is the finite-satisfiability input for the eventual elementary-
diagram compactness argument. -/
theorem finiteNormReductDiagram_approximately_realizedInExpansion
    (R : ℝ) (hR : 0 < R)
    {N : MultiStructure ReductSymbol}
    (hTheory : MultiSameCompleteTheory (reductStructure R hR) N)
    (fragment : FiniteElementaryDiagramFragment N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ rows : Fin fragment.rowVars → PositiveNormBall Y R,
      ∃ parameters : Fin fragment.parameterVars → PositiveNormBall Y R,
        ∀ i : Fin fragment.conditionCount,
          |((((fragment.formulas i).map includeReduct).realize
              (expansionStructure R hR) rows parameters : TruthValue) : ℝ) -
            ((fragment.targets i : TruthValue) : ℝ)| < ε :=
  fragment.approximately_realized_in_expansion includeReduct
    (expansionStructure R hR) hTheory ε hε

/-- The remaining elementary-embedding boundary for the norm-language reduct
of a positive `Y`-ball. -/
def NormReductEmbeddingProperty (R : ℝ) (hR : 0 < R) : Prop :=
  (expansionStructure R hR).HasSameTheoryReductEmbeddingProperty includeReduct

/-- The elementary-diagram compactness principle specialized to the norm
reduct of the expanded positive `Y`-ball. -/
def NormElementaryDiagramCompactness (R : ℝ) (hR : 0 < R) : Prop :=
  ElementaryDiagramCompactness includeReduct (expansionStructure R hR)

/-- Sequential elementary-diagram compactness specialized to the norm reduct
of the expanded positive `Y`-ball. -/
def NormSequentialElementaryDiagramCompactness
    (R : ℝ) (hR : 0 < R) : Prop :=
  SequentialElementaryDiagramCompactness includeReduct
    (expansionStructure R hR)

/-- A simultaneous sequential realization of each finite norm-reduct diagram
is enough for the exact elementary-diagram compactness principle, by the
many-predicate reduced-product Łoś theorem. -/
theorem normElementaryDiagramCompactness_of_sequential
    (R : ℝ) (hR : 0 < R)
    (hsequential : NormSequentialElementaryDiagramCompactness R hR) :
    NormElementaryDiagramCompactness R hR :=
  elementaryDiagramCompactness_of_sequential includeReduct
    (expansionStructure R hR) (expansionStructureBounds R hR) hsequential

/-- Unrestricted elementary-diagram compactness for the norm reduct of the
expanded positive `Y`-ball, proved by the finite-fragment directed metric
ultraproduct. -/
theorem normElementaryDiagramCompactness
    (R : ℝ) (hR : 0 < R) :
    NormElementaryDiagramCompactness R hR :=
  elementaryDiagramCompactness_of_bounds includeReduct
    (expansionStructure R hR) (expansionStructureBounds R hR)

/-- The specialized compactness principle implies the exact reduct-embedding
property.  Its finite-fragment premise is the preceding approximate diagram
theorem. -/
theorem normReductEmbeddingProperty_of_elementaryDiagramCompactness
    (R : ℝ) (hR : 0 < R)
    (hcompact : NormElementaryDiagramCompactness R hR) :
    NormReductEmbeddingProperty R hR :=
  hasSameTheoryReductEmbeddingProperty_of_elementaryDiagramCompactness
    includeReduct (expansionStructure R hR) hcompact

/-- The norm reduct has the exact same-theory reduct-embedding property,
without an additional compactness assumption. -/
theorem normReductEmbeddingProperty (R : ℝ) (hR : 0 < R) :
    NormReductEmbeddingProperty R hR :=
  normReductEmbeddingProperty_of_elementaryDiagramCompactness
    R hR (normElementaryDiagramCompactness R hR)

/-- Subject only to the isolated reduct-embedding property, NIP of the lifted
norm formula transfers from the complete expanded theory to the complete
norm-language reduct theory. -/
theorem normFormula_isNIPInReduct_of_expansionNIP
    (R : ℝ) (hR : 0 < R)
    (hembedding : NormReductEmbeddingProperty R hR)
    (hNIP : MultiFormula.IsNIPInCompleteTheory
      (expansionStructure R hR) (normFormula.map includeReduct)) :
    MultiFormula.IsNIPInCompleteTheory (reductStructure R hR) normFormula :=
  MultiFormula.nip_reduct_of_expansion includeReduct
    (expansionStructure R hR) normFormula hembedding hNIP

/-- Combining reconstruction equivalence with conditional reduct transfer:
NIP of the Hilbert--`q` reconstruction implies NIP of the norm formula in the
complete reduct theory. -/
theorem normFormula_isNIPInReduct_of_reconstructionFormula_isNIP
    (R : ℝ) (hR : 0 < R)
    (hembedding : NormReductEmbeddingProperty R hR)
    (hreconstruction : MultiFormula.IsNIPInCompleteTheory
      (expansionStructure R hR) reconstructionFormula) :
    MultiFormula.IsNIPInCompleteTheory (reductStructure R hR) normFormula :=
  normFormula_isNIPInReduct_of_expansionNIP R hR hembedding
    (liftedNormFormula_isNIP_of_reconstructionFormula_isNIP
      R hR hreconstruction)

/-- Unconditional reduct transfer: NIP of the lifted norm formula in the
complete expansion theory implies NIP of the norm formula in the complete
reduct theory. -/
theorem normFormula_isNIPInReduct
    (R : ℝ) (hR : 0 < R)
    (hNIP : MultiFormula.IsNIPInCompleteTheory
      (expansionStructure R hR) (normFormula.map includeReduct)) :
    MultiFormula.IsNIPInCompleteTheory (reductStructure R hR) normFormula :=
  normFormula_isNIPInReduct_of_expansionNIP R hR
    (normReductEmbeddingProperty R hR) hNIP

/-- The reconstruction-to-reduct NIP implication with elementary-diagram
compactness fully discharged. -/
theorem normFormula_isNIPInReduct_of_reconstructionNIP
    (R : ℝ) (hR : 0 < R)
    (hreconstruction : MultiFormula.IsNIPInCompleteTheory
      (expansionStructure R hR) reconstructionFormula) :
    MultiFormula.IsNIPInCompleteTheory (reductStructure R hR) normFormula :=
  normFormula_isNIPInReduct_of_reconstructionFormula_isNIP R hR
    (normReductEmbeddingProperty R hR) hreconstruction

end


end NormFormula.HalfGraph.Y.ContinuousLanguage
