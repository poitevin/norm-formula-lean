import Mathlib.Topology.Sequences
import NormFormula.ContinuousLogic.LocalTypeSpace
import NormFormula.ContinuousLogic.MultiTheoryIP

/-!
# The local-type BFT criterion

An infinite fixed-gap independence witness prevents pointwise sequential
compactness on the local parameter type space.  The proof uses compactness of
that space to realize one alternating limit profile from the finitely
satisfiable low/high constraints.  Thus the pointwise-subsequence property
implies NIP on the distinguished structure. The converse is proved below
through the open-prefix Ramsey lemma and the threshold-pair dichotomy.
The general unconditional wrapper requires no additional Lipschitz premise.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open Filter Set TopologicalSpace
open scoped Topology

universe u v w

namespace MultiFormula

attribute [local instance] MultiStructure.rowPseudoMetricSpace
  MultiStructure.rowNonempty

/-- A binary formula has IP on the distinguished structure itself when it has
one infinite fixed-gap witness there. -/
def HasIPOnStructure {Symbol : Type w}
    (M : MultiStructure.{u, v, w} Symbol)
    (φ : MultiFormula Symbol 1 1) : Prop :=
  ∃ low high : ℝ, low < high ∧ HasInfiniteIPWitness M φ low high

/-- NIP on the distinguished structure. -/
def IsNIPOnStructure {Symbol : Type w}
    (M : MultiStructure.{u, v, w} Symbol)
    (φ : MultiFormula Symbol 1 1) : Prop :=
  ¬ HasIPOnStructure M φ

/-- Independence of the low/high level-set pairs at fixed thresholds. -/
def ThresholdPairIndependent {α : Type*} (values : ℕ → α → ℝ)
    (low high : ℝ) : Prop :=
  ∀ E F : Finset ℕ, Disjoint E F →
    ∃ point : α,
      (∀ i ∈ E, values i point ≤ low) ∧
      (∀ i ∈ F, high ≤ values i point)


/-- A position-dependent sequence of frequent predicates can be met along one
strictly increasing sequence. At each step choose a witness beyond the
previous index. -/
theorem exists_strictMono_satisfying_of_positionwise_frequently
    {predicate : ℕ → ℕ → Prop}
    (hfrequent : ∀ position, ∃ᶠ n in atTop, predicate position n) :
    ∃ indices : ℕ → ℕ, StrictMono indices ∧
      ∀ position, predicate position (indices position) := by
  classical
  let candidate : ℕ → ℕ → ℕ := fun position ↦
    Classical.choose (extraction_of_frequently_atTop (hfrequent position))
  have hcandidateStrict : ∀ position, StrictMono (candidate position) :=
    fun position ↦
      (Classical.choose_spec
        (extraction_of_frequently_atTop (hfrequent position))).1
  have hcandidate : ∀ position n,
      predicate position (candidate position n) :=
    fun position ↦
      (Classical.choose_spec
        (extraction_of_frequently_atTop (hfrequent position))).2
  let indices : ℕ → ℕ := fun n ↦
    Nat.rec (candidate 0 0)
      (fun position previous ↦
        candidate (position + 1) (previous + 1)) n
  have hindicesZero : indices 0 = candidate 0 0 := rfl
  have hindicesSucc (n : ℕ) :
      indices (n + 1) = candidate (n + 1) (indices n + 1) := by
    simp only [indices]
  refine ⟨indices, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    rw [hindicesSucc]
    exact (Nat.lt_succ_self (indices n)).trans_le
      ((hcandidateStrict (n + 1)).id_le (indices n + 1))
  · intro position
    cases position with
    | zero =>
        rw [hindicesZero]
        exact hcandidate 0 0
    | succ n =>
        rw [hindicesSucc]
        exact hcandidate (n + 1) (indices n + 1)

/-- A sequence of real-valued functions is independent when one fixed gap
realizes every finite disjoint low/high prescription. This is the exact
topological-combinatorial hypothesis excluded by the BFT theorem. -/
def HasIndependentSequence {α : Type*} (values : ℕ → α → ℝ) : Prop :=
  ∃ low high : ℝ, low < high ∧
    ThresholdPairIndependent values low high

/-- The local-type evaluation functions indexed by a row sequence. -/
def localTypeEvaluationSequence {Symbol : Type w}
    {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1} (rows : ℕ → M.Row) :
    ℕ → LocalParameterType M φ → ℝ :=
  fun n type ↦ localTypeValue (rows n) type

/-- IP on the distinguished structure is exactly the existence of an
independent sequence of continuous coordinate functions on its local
parameter type space.

For the reverse implication, an independent pattern may initially be
realized only by a limit type. Shrinking the gap and using density of the
home parameters realizes each finite prescription back in the distinguished
structure. -/
theorem hasIPOnStructure_iff_exists_independent_localTypeEvaluationSequence
    {Symbol : Type w} {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1} :
    HasIPOnStructure M φ ↔
      ∃ rows : ℕ → M.Row,
        HasIndependentSequence (localTypeEvaluationSequence (φ := φ) rows) := by
  constructor
  · rintro ⟨low, high, hgap, rows, hrows⟩
    refine ⟨rows, low, high, hgap, ?_⟩
    intro E F hdisjoint
    obtain ⟨parameter, hlow, hhigh⟩ := hrows E F hdisjoint
    refine ⟨homeParameterType M φ parameter, ?_, ?_⟩
    · intro i hi
      change φ.binaryValue M (rows i) parameter ≤ low
      exact hlow i hi
    · intro i hi
      change high ≤ φ.binaryValue M (rows i) parameter
      exact hhigh i hi
  · rintro ⟨rows, low, high, hgap, hindependent⟩
    let low' : ℝ := (2 * low + high) / 3
    let high' : ℝ := (low + 2 * high) / 3
    have hlow_lt_low' : low < low' := by
      dsimp [low']
      linarith
    have hhigh'_lt_high : high' < high := by
      dsimp [high']
      linarith
    have hnewGap : low' < high' := by
      dsimp [low', high']
      linarith
    refine ⟨low', high', hnewGap, rows, ?_⟩
    intro E F hdisjoint
    obtain ⟨type, hlow, hhigh⟩ := hindependent E F hdisjoint
    let neighborhood : Set (M.Row → TruthValue) :=
      (⋂ i ∈ E,
        {profile | (profile (rows i) : ℝ) < low'}) ∩
      (⋂ i ∈ F,
        {profile | high' < (profile (rows i) : ℝ)})
    have hcoordinateContinuous : ∀ row : M.Row,
        Continuous fun profile : M.Row → TruthValue ↦
          (profile row : ℝ) := by
      intro row
      exact continuous_subtype_val.comp (continuous_apply row)
    have hneighborhoodOpen : IsOpen neighborhood := by
      apply IsOpen.inter
      · exact isOpen_biInter_finset fun i _ ↦
          isOpen_Iio.preimage (hcoordinateContinuous (rows i))
      · exact isOpen_biInter_finset fun i _ ↦
          isOpen_Ioi.preimage (hcoordinateContinuous (rows i))
    have htypeMem : type.1 ∈ neighborhood := by
      constructor
      · simp only [Set.mem_iInter]
        intro i hi
        exact (hlow i hi).trans_lt hlow_lt_low'
      · simp only [Set.mem_iInter]
        intro i hi
        exact hhigh'_lt_high.trans_le (hhigh i hi)
    obtain ⟨profile, hprofileNeighborhood, parameter, hparameter⟩ :=
      mem_closure_iff.mp type.2 neighborhood hneighborhoodOpen htypeMem
    subst profile
    refine ⟨parameter, ?_, ?_⟩
    · intro i hi
      exact le_of_lt (Set.mem_iInter.mp
        (Set.mem_iInter.mp hprofileNeighborhood.1 i) hi)
    · intro i hi
      exact le_of_lt (Set.mem_iInter.mp
        (Set.mem_iInter.mp hprofileNeighborhood.2 i) hi)

/-- NIP on the distinguished structure is therefore exactly the absence of
an independent local-type evaluation sequence. -/
theorem isNIPOnStructure_iff_no_independent_localTypeEvaluationSequence
    {Symbol : Type w} {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1} :
    IsNIPOnStructure M φ ↔
      ∀ rows : ℕ → M.Row,
        ¬ HasIndependentSequence
          (localTypeEvaluationSequence (φ := φ) rows) := by
  constructor
  · intro hNIP rows hindependent
    apply hNIP
    exact
      hasIPOnStructure_iff_exists_independent_localTypeEvaluationSequence.mpr
        ⟨rows, hindependent⟩
  · intro hNoIndependent hIP
    obtain ⟨rows, hindependent⟩ :=
      hasIPOnStructure_iff_exists_independent_localTypeEvaluationSequence.mp hIP
    exact hNoIndependent rows hindependent

/-- Pointwise sequential compactness for one sequence of real-valued
functions. -/
def HasPointwiseConvergentSubsequence {α : Type*}
    (values : ℕ → α → ℝ) : Prop :=
  ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
    ∀ point : α, ∃ limit : ℝ,
      Tendsto (fun n ↦ values (subsequence n) point) atTop (𝓝 limit)

/-- A sequence contains an independent subsequence. This is the second
alternative in the BFT dichotomy; the original sequence itself need not be
independent. -/
def HasIndependentSubsequence {α : Type*}
    (values : ℕ → α → ℝ) : Prop :=
  ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
    HasIndependentSequence
      (fun n point ↦ values (subsequence n) point)

/-- A strictly increasing enumeration of a subsequence, bundled so that
successive countable refinements can be defined recursively. -/
structure NatSubsequence where
  indices : ℕ → ℕ
  strictMono_indices : StrictMono indices

instance : CoeFun NatSubsequence (fun _ ↦ ℕ → ℕ) :=
  ⟨NatSubsequence.indices⟩

namespace NatSubsequence

/-- The identity subsequence. -/
def id : NatSubsequence :=
  ⟨fun n ↦ n, strictMono_id⟩

/-- Composition of two subsequence enumerations. -/
def comp (outer inner : NatSubsequence) : NatSubsequence :=
  ⟨outer ∘ inner,
    outer.strictMono_indices.comp inner.strictMono_indices⟩

@[simp]
theorem comp_apply (outer inner : NatSubsequence) (n : ℕ) :
    outer.comp inner n = outer (inner n) :=
  rfl

end NatSubsequence

/-- The exact abstract BFT dichotomy needed below: a uniformly `[0,1]`-valued
sequence of continuous functions either has a pointwise convergent
subsequence or is independent. Isolating this proposition makes the remaining
deep topological theorem independent of the continuous-logic syntax. -/
def BFTPointwiseDichotomy (α : Type*) [TopologicalSpace α] : Prop :=
  ∀ values : ℕ → α → ℝ,
    (∀ n, Continuous (values n)) →
    (∀ n point, values n point ∈ Set.Icc (0 : ℝ) 1) →
      HasPointwiseConvergentSubsequence values ∨
        HasIndependentSubsequence values


/-- The elementary compactness half of the BFT dichotomy. A continuous
independent sequence on a compact space cannot converge pointwise along any
subsequence: finite independence realizes alternating finite constraints,
compactness realizes all of them at one point, and the even and odd limits
then contradict the fixed gap. -/
theorem HasIndependentSequence.no_pointwiseConvergence_along
    {α : Type*} [TopologicalSpace α] [CompactSpace α]
    {values : ℕ → α → ℝ}
    (hindependentSequence : HasIndependentSequence values)
    (hcontinuous : ∀ n, Continuous (values n))
    (subsequence : ℕ → ℕ) (hsubsequence : StrictMono subsequence) :
    ¬ ∀ point : α, ∃ limit : ℝ,
        Tendsto (fun n ↦ values (subsequence n) point) atTop (𝓝 limit) := by
  classical
  obtain ⟨low, high, hgap, hindependent⟩ := hindependentSequence
  let constraint : ℕ → Set α := fun n ↦
    if Even n then
      {point | high ≤ values (subsequence n) point}
    else
      {point | values (subsequence n) point ≤ low}
  have hconstraintClosed : ∀ n, IsClosed (constraint n) := by
    intro n
    dsimp [constraint]
    split_ifs
    · exact isClosed_Ici.preimage (hcontinuous (subsequence n))
    · exact isClosed_Iic.preimage (hcontinuous (subsequence n))
  have hfinite : ∀ indices : Finset ℕ,
      ((Set.univ : Set α) ∩ ⋂ n ∈ indices, constraint n).Nonempty := by
    intro indices
    let lowIndices : Finset ℕ :=
      (indices.filter fun n ↦ ¬ Even n).image subsequence
    let highIndices : Finset ℕ :=
      (indices.filter Even).image subsequence
    have hdisjoint : Disjoint lowIndices highIndices := by
      rw [Finset.disjoint_left]
      intro i hiLow hiHigh
      obtain ⟨n, hn, hni⟩ := Finset.mem_image.mp hiLow
      obtain ⟨m, hm, hmi⟩ := Finset.mem_image.mp hiHigh
      have hnm : n = m := hsubsequence.injective (hni.trans hmi.symm)
      have hnOdd : ¬ Even n := (Finset.mem_filter.mp hn).2
      have hmEven : Even m := (Finset.mem_filter.mp hm).2
      exact hnOdd (hnm ▸ hmEven)
    obtain ⟨point, hlow, hhigh⟩ :=
      hindependent lowIndices highIndices hdisjoint
    refine ⟨point, Set.mem_univ _, ?_⟩
    simp only [Set.mem_iInter]
    intro n hn
    dsimp [constraint]
    split_ifs with hnEven
    · apply hhigh (subsequence n)
      exact Finset.mem_image.mpr
        ⟨n, Finset.mem_filter.mpr ⟨hn, hnEven⟩, rfl⟩
    · apply hlow (subsequence n)
      exact Finset.mem_image.mpr
        ⟨n, Finset.mem_filter.mpr ⟨hn, hnEven⟩, rfl⟩
  obtain ⟨alternatingPoint, _, hpoint⟩ :=
    isCompact_univ.inter_iInter_nonempty
      constraint hconstraintClosed hfinite
  have hpointAll : ∀ n, alternatingPoint ∈ constraint n :=
    Set.mem_iInter.mp hpoint
  intro hconverges
  obtain ⟨limit, hlimit⟩ := hconverges alternatingPoint
  have hevenMono : StrictMono (fun n : ℕ ↦ 2 * n) := by
    intro m n hmn
    change 2 * m < 2 * n
    omega
  have hoddMono : StrictMono (fun n : ℕ ↦ 2 * n + 1) := by
    intro m n hmn
    change 2 * m + 1 < 2 * n + 1
    omega
  have hevenLimit := hlimit.comp hevenMono.tendsto_atTop
  have hoddLimit := hlimit.comp hoddMono.tendsto_atTop
  have hevenBound : ∀ n : ℕ,
      high ≤ values (subsequence (2 * n)) alternatingPoint := by
    intro n
    have hn := hpointAll (2 * n)
    simpa [constraint] using hn
  have hoddBound : ∀ n : ℕ,
      values (subsequence (2 * n + 1)) alternatingPoint ≤ low := by
    intro n
    have hn := hpointAll (2 * n + 1)
    simpa [constraint, show ¬ Even (2 * n + 1) by
      exact Nat.not_even_iff_odd.mpr ⟨n, rfl⟩] using hn
  have hhighLimit : high ≤ limit :=
    ge_of_tendsto hevenLimit (Eventually.of_forall hevenBound)
  have hlimitLow : limit ≤ low :=
    le_of_tendsto hoddLimit (Eventually.of_forall hoddBound)
  linarith


/-- Convergence of the disjoint low/high level-set pairs on a subset: at each
point the sequence eventually avoids the low side or eventually avoids the
high side. -/
def ThresholdPairConvergesOn {α : Type*} (values : ℕ → α → ℝ)
    (low high : ℝ) (subset : Set α) : Prop :=
  ∀ point ∈ subset,
    (∀ᶠ n in atTop, low < values n point) ∨
      (∀ᶠ n in atTop, values n point < high)

/-- Global convergence of the low/high level-set pairs. -/
def ThresholdPairConverges {α : Type*} (values : ℕ → α → ℝ)
    (low high : ℝ) : Prop :=
  ThresholdPairConvergesOn values low high Set.univ


/-- Threshold-pair convergence is inherited by subsequences. -/
theorem ThresholdPairConvergesOn.comp_strictMono
    {α : Type*} {values : ℕ → α → ℝ} {subset : Set α}
    {low high : ℝ}
    (hconverges : ThresholdPairConvergesOn values low high subset)
    (subsequence : ℕ → ℕ) (hsubsequence : StrictMono subsequence) :
    ThresholdPairConvergesOn
      (fun n point ↦ values (subsequence n) point) low high subset := by
  intro point hpoint
  rcases hconverges point hpoint with hlow | hhigh
  · exact Or.inl (hsubsequence.tendsto_atTop.eventually hlow)
  · exact Or.inr (hsubsequence.tendsto_atTop.eventually hhigh)

/-- An increasing enumeration whose range is contained in the range of
another increasing enumeration factors through it by an increasing map. -/
theorem strictMono_factor_of_range_subset
    {first second : ℕ → ℕ}
    (hfirst : StrictMono first) (hsecond : StrictMono second)
    (hrange : Set.range second ⊆ Set.range first) :
    ∃ factor : ℕ → ℕ, StrictMono factor ∧
      second = first ∘ factor := by
  obtain ⟨factor, hfactor⟩ :=
    Set.range_subset_range_iff_exists_comp.mp hrange
  refine ⟨factor, ?_, hfactor⟩
  intro m n hmn
  apply hfirst.lt_iff_lt.mp
  simpa only [hfactor, Function.comp_apply] using hsecond hmn

/-- The diagonal of a decreasing tower of subsequences is itself a
subsequence, and each of its tails factors through the corresponding tower
level. This is the bookkeeping lemma behind countable diagonal refinement. -/
theorem exists_strictMono_diagonal_of_nested
    (sequences : ℕ → ℕ → ℕ)
    (hstrict : ∀ n, StrictMono (sequences n))
    (hnested : ∀ n,
      Set.range (sequences (n + 1)) ⊆ Set.range (sequences n)) :
    ∃ diagonal : ℕ → ℕ, StrictMono diagonal ∧
      ∀ k, ∃ factor : ℕ → ℕ, StrictMono factor ∧
        (fun n ↦ diagonal (k + n)) = sequences k ∘ factor := by
  let diagonal : ℕ → ℕ := fun n ↦ sequences n n
  have hdiagonal : StrictMono diagonal := by
    apply strictMono_nat_of_lt_succ
    intro n
    obtain ⟨factor, hfactor, heq⟩ :=
      strictMono_factor_of_range_subset
        (hstrict n) (hstrict (n + 1)) (hnested n)
    calc
      diagonal n < sequences n (n + 1) :=
        hstrict n (Nat.lt_succ_self n)
      _ ≤ sequences n (factor (n + 1)) :=
        (hstrict n).monotone (hfactor.id_le (n + 1))
      _ = diagonal (n + 1) := by
        simp only [diagonal, heq, Function.comp_apply]
  refine ⟨diagonal, hdiagonal, ?_⟩
  have hRange : ∀ k n,
      Set.range (sequences (k + n)) ⊆ Set.range (sequences k) := by
    intro k n
    induction n with
    | zero => simp
    | succ n ih =>
        exact (by
          simpa only [Nat.add_assoc, Nat.add_comm 1] using
            (hnested (k + n)).trans ih)
  intro k
  have htail : StrictMono (fun n ↦ diagonal (k + n)) :=
    hdiagonal.comp fun _ _ hmn ↦ Nat.add_lt_add_left hmn k
  apply strictMono_factor_of_range_subset (hstrict k) htail
  rintro _ ⟨n, rfl⟩
  exact hRange k n ⟨k + n, rfl⟩

/-- A convergent threshold pair rules out two subsequential scalar limits
lying strictly on opposite sides of its gap. -/
theorem ThresholdPairConverges.not_two_subsequentialLimits
    {α : Type*} {values : ℕ → α → ℝ} {low high : ℝ}
    (hconverges : ThresholdPairConverges values low high)
    (point : α)
    {firstSubsequence secondSubsequence : ℕ → ℕ}
    (hfirstSubsequence : StrictMono firstSubsequence)
    (hsecondSubsequence : StrictMono secondSubsequence)
    {firstLimit secondLimit : ℝ}
    (hfirstLimit : Tendsto
      (fun n ↦ values (firstSubsequence n) point)
      atTop (𝓝 firstLimit))
    (hsecondLimit : Tendsto
      (fun n ↦ values (secondSubsequence n) point)
      atTop (𝓝 secondLimit))
    (hfirstLow : firstLimit < low) (hhighSecond : high < secondLimit) :
    False := by
  rcases hconverges point (Set.mem_univ point) with hAvoidLow | hAvoidHigh
  · have hEventuallyAboveLow :=
      hfirstSubsequence.tendsto_atTop.eventually hAvoidLow
    have hEventuallyBelowLow :=
      hfirstLimit.eventually (Iio_mem_nhds hfirstLow)
    exact (hEventuallyAboveLow.and hEventuallyBelowLow).exists.elim
      fun _ h ↦ (not_lt_of_ge h.1.le h.2)
  · have hEventuallyBelowHigh :=
      hsecondSubsequence.tendsto_atTop.eventually hAvoidHigh
    have hEventuallyAboveHigh :=
      hsecondLimit.eventually (Ioi_mem_nhds hhighSecond)
    exact (hEventuallyBelowHigh.and hEventuallyAboveHigh).exists.elim
      fun _ h ↦ (not_lt_of_ge h.2.le h.1)

/-- If every rational threshold pair converges, all subsequential limits at a
fixed point agree. Rational density places a strict pair between any two
distinct candidate limits, contradicting the preceding separation lemma. -/
theorem subsequentialLimits_eq_of_rational_thresholdPairConvergence
    {α : Type*} {values : ℕ → α → ℝ}
    (hconverges : ∀ q r : ℚ, q < r →
      ThresholdPairConverges values (q : ℝ) (r : ℝ))
    (point : α)
    {firstSubsequence secondSubsequence : ℕ → ℕ}
    (hfirstSubsequence : StrictMono firstSubsequence)
    (hsecondSubsequence : StrictMono secondSubsequence)
    {firstLimit secondLimit : ℝ}
    (hfirstLimit : Tendsto
      (fun n ↦ values (firstSubsequence n) point)
      atTop (𝓝 firstLimit))
    (hsecondLimit : Tendsto
      (fun n ↦ values (secondSubsequence n) point)
      atTop (𝓝 secondLimit)) :
    firstLimit = secondLimit := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨q, hfirstQ, hqSecond⟩ := exists_rat_btwn hlt
    obtain ⟨r, hqR, hrSecond⟩ := exists_rat_btwn hqSecond
    have hqr : q < r := by exact_mod_cast hqR
    exact (hconverges q r hqr).not_two_subsequentialLimits point
      hfirstSubsequence hsecondSubsequence hfirstLimit hsecondLimit
      hfirstQ hrSecond
  · obtain ⟨q, hsecondQ, hqFirst⟩ := exists_rat_btwn hgt
    obtain ⟨r, hqR, hrFirst⟩ := exists_rat_btwn hqFirst
    have hqr : q < r := by exact_mod_cast hqR
    exact (hconverges q r hqr).not_two_subsequentialLimits point
      hsecondSubsequence hfirstSubsequence hsecondLimit hfirstLimit
      hsecondQ hrFirst

/-- For a uniformly `[0,1]`-valued sequence, convergence of every rational
threshold pair implies pointwise scalar convergence. Compactness first gives
one subsequential limit at each point. If the full scalar sequence failed to
converge to it, a subsequence uniformly separated from that limit would have a
second convergent subsequence; rational threshold-pair convergence forces the
two limits to agree, while closedness of the separation inequality forces
them apart. -/
theorem pointwiseConvergence_of_rational_thresholdPairConvergence
    {α : Type*} {values : ℕ → α → ℝ}
    (hbounded : ∀ n point, values n point ∈ Set.Icc (0 : ℝ) 1)
    (hconverges : ∀ q r : ℚ, q < r →
      ThresholdPairConverges values (q : ℝ) (r : ℝ)) :
    ∀ point : α, ∃ limit : ℝ,
      Tendsto (fun n ↦ values n point) atTop (𝓝 limit) := by
  intro point
  let scalarProfiles : ℕ → TruthValue :=
    fun n ↦ ⟨values n point, hbounded n point⟩
  obtain ⟨firstProfile, firstSubsequence, hfirstSubsequence,
      hfirstProfile⟩ :=
    SeqCompactSpace.tendsto_subseq scalarProfiles
  have hfirstLimit : Tendsto
      (fun n ↦ values (firstSubsequence n) point)
      atTop (𝓝 (firstProfile : ℝ)) := by
    simpa [scalarProfiles, Function.comp_def] using
      continuous_subtype_val.continuousAt.tendsto.comp hfirstProfile
  refine ⟨firstProfile, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra hnot
  push Not at hnot
  have hfrequent : ∃ᶠ n in atTop,
      ε ≤ dist (values n point) (firstProfile : ℝ) := by
    rw [frequently_atTop]
    exact hnot
  obtain ⟨badSubsequence, hbadSubsequence, hbad⟩ :=
    extraction_of_frequently_atTop hfrequent
  let badProfiles : ℕ → TruthValue :=
    fun n ↦ scalarProfiles (badSubsequence n)
  obtain ⟨secondProfile, furtherSubsequence, hfurtherSubsequence,
      hsecondProfile⟩ :=
    SeqCompactSpace.tendsto_subseq badProfiles
  let secondSubsequence : ℕ → ℕ := badSubsequence ∘ furtherSubsequence
  have hsecondSubsequence : StrictMono secondSubsequence :=
    hbadSubsequence.comp hfurtherSubsequence
  have hsecondLimit : Tendsto
      (fun n ↦ values (secondSubsequence n) point)
      atTop (𝓝 (secondProfile : ℝ)) := by
    simpa [secondSubsequence, badProfiles, scalarProfiles,
      Function.comp_def] using
      continuous_subtype_val.continuousAt.tendsto.comp hsecondProfile
  have hlimitsEqual : (firstProfile : ℝ) = (secondProfile : ℝ) :=
    subsequentialLimits_eq_of_rational_thresholdPairConvergence
      hconverges point hfirstSubsequence hsecondSubsequence
      hfirstLimit hsecondLimit
  have hdistLimit : Tendsto
      (fun n ↦ dist (values (secondSubsequence n) point)
        (firstProfile : ℝ))
      atTop (𝓝 (dist (secondProfile : ℝ) (firstProfile : ℝ))) :=
    hsecondLimit.dist tendsto_const_nhds
  have hseparated : ε ≤ dist (secondProfile : ℝ) (firstProfile : ℝ) :=
    ge_of_tendsto hdistLimit <| Eventually.of_forall fun n ↦
      hbad (furtherSubsequence n)
  rw [← hlimitsEqual, dist_self] at hseparated
  exact (not_le_of_gt hε) hseparated

/-- The pure set-theoretic level-pair dichotomy that forms the combinatorial
core of Rosenthal/BFT: at fixed disjoint thresholds, some subsequence has
convergent level-set pairs or independent level-set pairs. -/
def ThresholdPairSubsequenceDichotomy : Prop :=
  ∀ (α : Type u) (values : ℕ → α → ℝ) (low high : ℝ), low < high →
    ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      (ThresholdPairConverges
          (fun n point ↦ values (subsequence n) point) low high ∨
        ThresholdPairIndependent
          (fun n point ↦ values (subsequence n) point) low high)


/-- Realization of the alternating low/high word along one finite prefix of
an infinite index sequence. -/
def AlternatingPrefixRealized {α : Type*} (values : ℕ → α → ℝ)
    (low high : ℝ) (indices : ℕ → ℕ) (length : ℕ) : Prop :=
  ∃ point : α, ∀ i : Fin length,
    if Even (i : ℕ) then values (indices i) point ≤ low
    else high ≤ values (indices i) point

/-- Every finite alternating prefix of an infinite index sequence is
realized, possibly by a different point at each length. -/
def AllAlternatingPrefixesRealized {α : Type*}
    (values : ℕ → α → ℝ) (low high : ℝ)
    (indices : ℕ → ℕ) : Prop :=
  ∀ length, AlternatingPrefixRealized values low high indices length

/-- The set of index sequences whose every finite alternating prefix is
realized is closed in Baire space. Failure is witnessed by one finite prefix,
and the cylinder fixing that prefix is an open neighborhood of failure. -/
theorem isClosed_allAlternatingPrefixesRealized
    {α : Type*} (values : ℕ → α → ℝ) (low high : ℝ) :
    IsClosed {indices : ℕ → ℕ |
      AllAlternatingPrefixesRealized values low high indices} := by
  classical
  rw [← isOpen_compl_iff]
  rw [isOpen_iff_mem_nhds]
  intro indices hindices
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hindices ⊢
  obtain ⟨length, hlength⟩ :=
    not_forall.mp (show ¬ ∀ length,
      AlternatingPrefixRealized values low high indices length from hindices)
  let cylinder : Set (ℕ → ℕ) :=
    ⋂ i : Fin length, {other | other i = indices i}
  have hcylinderOpen : IsOpen cylinder := by
    apply isOpen_iInter_of_finite
    intro i
    change IsOpen ((fun other : ℕ → ℕ ↦ other i) ⁻¹' {indices i})
    have hcontinuous : Continuous
        (fun other : ℕ → ℕ ↦ other (i : ℕ)) :=
      continuous_apply (i : ℕ)
    exact (isOpen_discrete ({indices i} : Set ℕ)).preimage hcontinuous
  have hindicesCylinder : indices ∈ cylinder := by
    simp [cylinder]
  apply Filter.mem_of_superset
    (hcylinderOpen.mem_nhds hindicesCylinder)
  intro other hother
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
  intro hotherAlternating
  apply hlength
  obtain ⟨point, hpoint⟩ := hotherAlternating length
  refine ⟨point, ?_⟩
  intro i
  have heq : other i = indices i :=
    Set.mem_iInter.mp hother i
  simpa only [heq] using hpoint i

/-- The closed-set Galvin--Prikry theorem in the exact subsequence form used
by Rosenthal's pair lemma. This is the correct remaining Ramsey input: every
closed set of Baire-space sequences is homogeneous on all subsequences of
some increasing base sequence. -/
def GalvinPrikryClosedSubsequenceRamsey : Prop :=
  ∀ closedSet : Set (ℕ → ℕ), IsClosed closedSet →
    ∃ base : ℕ → ℕ, StrictMono base ∧
      ((∀ subsequence : ℕ → ℕ, StrictMono subsequence →
          base ∘ subsequence ∈ closedSet) ∨
        (∀ subsequence : ℕ → ℕ, StrictMono subsequence →
          base ∘ subsequence ∉ closedSet))

/-- The basic Baire-space cylinder determined by a finite initial prefix. -/
def FinitePrefixCylinder {length : ℕ} (stem : Fin length → ℕ) :
    Set (ℕ → ℕ) :=
  {sequence | ∀ i : Fin length, sequence (i : ℕ) = stem i}


/-- Every point of an open subset of Baire space has a neighborhood obtained
by fixing one finite initial segment. -/
theorem exists_finitePrefixCylinder_subset_of_isOpen
    {openSet : Set (ℕ → ℕ)} (hopen : IsOpen openSet)
    {sequence : ℕ → ℕ} (hsequence : sequence ∈ openSet) :
    ∃ length : ℕ,
      FinitePrefixCylinder (fun i : Fin length ↦ sequence i) ⊆ openSet := by
  classical
  obtain ⟨coordinates, neighborhoods, hneighborhoods, hsubset⟩ :=
    isOpen_pi_iff.mp hopen sequence hsequence
  let length : ℕ := coordinates.sup id + 1
  refine ⟨length, ?_⟩
  intro other hother
  apply hsubset
  intro coordinate hcoordinate
  have hle : coordinate ≤ coordinates.sup id :=
    Finset.le_sup (f := id) hcoordinate
  have hlt : coordinate < length := by
    dsimp only [length]
    omega
  have heq := hother ⟨coordinate, hlt⟩
  rw [heq]
  exact (hneighborhoods coordinate hcoordinate).2

/-- Galvin's open-prefix lemma in the exact combinatorial form needed for the
closed-set theorem. For every family of finite prefixes, some increasing base
sequence has the property that every subsequence has a prefix in the family,
or no subsequence has such a prefix. -/
def GalvinOpenPrefixRamsey : Prop :=
  ∀ barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop,
    ∃ base : ℕ → ℕ, StrictMono base ∧
      ((∀ subsequence : ℕ → ℕ, StrictMono subsequence →
          ∃ length : ℕ,
            barrier length (fun i ↦ base (subsequence i))) ∨
        (∀ subsequence : ℕ → ℕ, StrictMono subsequence →
          ∀ length : ℕ,
            ¬ barrier length (fun i ↦ base (subsequence i))))

/-- Galvin's open-prefix lemma implies the closed-set Galvin--Prikry theorem.
Apply the prefix lemma to cylinders contained in the open complement. In the
positive branch every subsequence lies in that complement; in the negative
branch openness would produce a forbidden witnessing cylinder. -/
theorem galvinPrikryClosedSubsequenceRamsey_of_openPrefixRamsey
    (hOpenPrefix : GalvinOpenPrefixRamsey) :
    GalvinPrikryClosedSubsequenceRamsey := by
  intro closedSet hclosed
  let barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop :=
    fun _ stem ↦ FinitePrefixCylinder stem ⊆ closedSetᶜ
  obtain ⟨base, hbase, hHit | hAvoid⟩ := hOpenPrefix barrier
  · refine ⟨base, hbase, Or.inr ?_⟩
    intro subsequence hsubsequence hmem
    obtain ⟨length, hbarrier⟩ := hHit subsequence hsubsequence
    have hcomposition : base ∘ subsequence ∈
        FinitePrefixCylinder
          (fun i : Fin length ↦ base (subsequence i)) := by
      exact fun _ ↦ rfl
    exact hbarrier hcomposition hmem
  · refine ⟨base, hbase, Or.inl ?_⟩
    intro subsequence hsubsequence
    by_contra hnotMem
    have hmemComplement : base ∘ subsequence ∈ closedSetᶜ := hnotMem
    obtain ⟨length, hcylinder⟩ :=
      exists_finitePrefixCylinder_subset_of_isOpen
        hclosed.isOpen_compl hmemComplement
    exact hAvoid subsequence hsubsequence length hcylinder

/-- An infinite tail accepts a finite stem when every further subsequence has
a finite initial extension that belongs to the prescribed prefix family. -/
def PrefixAccepts
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    {stemLength : ℕ} (stem : Fin stemLength → ℕ)
    (tail : ℕ → ℕ) : Prop :=
  ∀ subsequence : ℕ → ℕ, StrictMono subsequence →
    ∃ extensionLength : ℕ,
      barrier (stemLength + extensionLength)
        (Fin.append stem
          (fun i : Fin extensionLength ↦ tail (subsequence i)))

/-- An infinite tail rejects a finite stem when no further subsequence of the
tail accepts that stem. This hereditary form is what supports fusion. -/
def PrefixRejects
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    {stemLength : ℕ} (stem : Fin stemLength → ℕ)
    (tail : ℕ → ℕ) : Prop :=
  ∀ subsequence : ℕ → ℕ, StrictMono subsequence →
    ¬ PrefixAccepts barrier stem (tail ∘ subsequence)

/-- A stem already belonging to the barrier is accepted on every tail, using
a zero-length extension. -/
theorem prefixAccepts_of_barrier
    {barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop}
    {stemLength : ℕ} {stem : Fin stemLength → ℕ}
    (hbarrier : barrier stemLength stem) (tail : ℕ → ℕ) :
    PrefixAccepts barrier stem tail := by
  intro subsequence _hsubsequence
  refine ⟨0, ?_⟩
  have hempty : (fun i : Fin 0 ↦ tail (subsequence i)) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  rw [hempty, Fin.append_elim0]
  simpa only [Function.comp_apply] using hbarrier

/-- Rejection is invariant under heterogeneous equality of finite stems. -/
theorem PrefixRejects.congr_heq
    {barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop}
    {firstLength secondLength : ℕ}
    {firstStem : Fin firstLength → ℕ}
    {secondStem : Fin secondLength → ℕ}
    {tail : ℕ → ℕ}
    (hrejects : PrefixRejects barrier firstStem tail)
    (hlength : firstLength = secondLength)
    (hstems : HEq firstStem secondStem) :
    PrefixRejects barrier secondStem tail := by
  subst secondLength
  rw [eq_of_heq hstems] at hrejects
  exact hrejects

/-- Acceptance is inherited by passing to a further subsequence of the
tail. -/
theorem PrefixAccepts.subsequence
    {barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop}
    {stemLength : ℕ} {stem : Fin stemLength → ℕ}
    {tail subsequence : ℕ → ℕ}
    (haccepts : PrefixAccepts barrier stem tail)
    (hsubsequence : StrictMono subsequence) :
    PrefixAccepts barrier stem (tail ∘ subsequence) := by
  intro further hfurther
  simpa only [Function.comp_apply] using
    haccepts (subsequence ∘ further) (hsubsequence.comp hfurther)

/-- Rejection is inherited by passing to a further subsequence of the tail. -/
theorem PrefixRejects.subsequence
    {barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop}
    {stemLength : ℕ} {stem : Fin stemLength → ℕ}
    {tail subsequence : ℕ → ℕ}
    (hrejects : PrefixRejects barrier stem tail)
    (hsubsequence : StrictMono subsequence) :
    PrefixRejects barrier stem (tail ∘ subsequence) := by
  intro further hfurther haccepts
  apply hrejects (subsequence ∘ further) (hsubsequence.comp hfurther)
  simpa only [Function.comp_apply] using haccepts

/-- Every finite stem can be decided after thinning an infinite tail: either
the thinned tail accepts it, or no further thinning can accept it. -/
theorem exists_subsequence_prefixAccepts_or_prefixRejects
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    {stemLength : ℕ} (stem : Fin stemLength → ℕ)
    (tail : ℕ → ℕ) :
    ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      (PrefixAccepts barrier stem (tail ∘ subsequence) ∨
        PrefixRejects barrier stem (tail ∘ subsequence)) := by
  classical
  by_cases haccepts : ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
        PrefixAccepts barrier stem (tail ∘ subsequence)
  · obtain ⟨subsequence, hsubsequence, haccepts⟩ := haccepts
    exact ⟨subsequence, hsubsequence, Or.inl haccepts⟩
  · refine ⟨id, strictMono_id, Or.inr ?_⟩
    intro further hfurther hfurtherAccepts
    apply haccepts
    refine ⟨further, hfurther, ?_⟩
    simpa only [Function.comp_apply, id_eq] using hfurtherAccepts


/-- The countable type of all finite natural-number stems. Enumerating this
type lets the fusion decide every possible stem without carrying a dependent
finite-stage state. -/
abbrev FiniteNatStem := Σ length : ℕ, Fin length → ℕ

noncomputable instance : Encodable FiniteNatStem :=
  Encodable.ofCountable FiniteNatStem

/-- A total enumeration of finite stems; undecodable codes default to the
empty stem. -/
noncomputable def enumeratedFiniteNatStem (code : ℕ) : FiniteNatStem :=
  (Encodable.decode code).getD ⟨0, Fin.elim0⟩

/-- Every finite stem occurs in the enumeration. -/
theorem enumeratedFiniteNatStem_surjective :
    Function.Surjective enumeratedFiniteNatStem := by
  intro stem
  refine ⟨Encodable.encode stem, ?_⟩
  simp [enumeratedFiniteNatStem, Encodable.encodek]

/-- A bundled thinning that decides one enumerated stem. -/
noncomputable def prefixDecisionSubsequence
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    (stem : FiniteNatStem) (tail : ℕ → ℕ) : NatSubsequence :=
  ⟨Classical.choose
      (exists_subsequence_prefixAccepts_or_prefixRejects
        barrier stem.2 tail),
    (Classical.choose_spec
      (exists_subsequence_prefixAccepts_or_prefixRejects
        barrier stem.2 tail)).1⟩

/-- The bundled decision thinning has the promised accept-or-reject result. -/
theorem prefixDecisionSubsequence_spec
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    (stem : FiniteNatStem) (tail : ℕ → ℕ) :
    PrefixAccepts barrier stem.2
        (tail ∘ prefixDecisionSubsequence barrier stem tail) ∨
      PrefixRejects barrier stem.2
        (tail ∘ prefixDecisionSubsequence barrier stem tail) :=
  (Classical.choose_spec
    (exists_subsequence_prefixAccepts_or_prefixRejects
      barrier stem.2 tail)).2

/-- The decreasing decision tower: at stage `n + 1`, refine stage `n` just
enough to decide the `n`th enumerated finite stem. -/
noncomputable def prefixDecisionTower
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop) :
    ℕ → NatSubsequence
  | 0 => NatSubsequence.id
  | n + 1 =>
      (prefixDecisionTower barrier n).comp
        (prefixDecisionSubsequence barrier
          (enumeratedFiniteNatStem n) (prefixDecisionTower barrier n))

/-- Consecutive levels of the decision tower are nested subsequences. -/
theorem prefixDecisionTower_succ
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop) (n : ℕ) :
    prefixDecisionTower barrier (n + 1) =
      (prefixDecisionTower barrier n).comp
        (prefixDecisionSubsequence barrier
          (enumeratedFiniteNatStem n) (prefixDecisionTower barrier n)) := by
  rfl

/-- The stem scheduled at stage `n` is decided at tower level `n + 1`. -/
theorem prefixDecisionTower_decides
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop) (n : ℕ) :
    PrefixAccepts barrier (enumeratedFiniteNatStem n).2
        (prefixDecisionTower barrier (n + 1)) ∨
      PrefixRejects barrier (enumeratedFiniteNatStem n).2
        (prefixDecisionTower barrier (n + 1)) := by
  simpa only [prefixDecisionTower_succ, NatSubsequence.comp_apply,
    Function.comp_apply] using
      prefixDecisionSubsequence_spec barrier
        (enumeratedFiniteNatStem n) (prefixDecisionTower barrier n)

/-- Every level of the decision tower is strictly increasing. -/
theorem prefixDecisionTower_strictMono
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop) (n : ℕ) :
    StrictMono (prefixDecisionTower barrier n) :=
  (prefixDecisionTower barrier n).strictMono_indices

/-- The range of each successor tower level is contained in the preceding
one, as required by countable diagonal refinement. -/
theorem prefixDecisionTower_range_succ_subset
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop) (n : ℕ) :
    Set.range (prefixDecisionTower barrier (n + 1)) ⊆
      Set.range (prefixDecisionTower barrier n) := by
  rintro _ ⟨index, rfl⟩
  refine ⟨prefixDecisionSubsequence barrier
    (enumeratedFiniteNatStem n) (prefixDecisionTower barrier n) index, ?_⟩
  rfl

/-- A single increasing diagonal through the decision tower; every diagonal
tail factors increasingly through the corresponding tower level. -/
theorem exists_prefixDecisionDiagonal
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop) :
    ∃ diagonal : ℕ → ℕ, StrictMono diagonal ∧
      ∀ k, ∃ factor : ℕ → ℕ, StrictMono factor ∧
        (fun n ↦ diagonal (k + n)) =
          prefixDecisionTower barrier k ∘ factor := by
  exact exists_strictMono_diagonal_of_nested
    (fun n ↦ prefixDecisionTower barrier n)
    (prefixDecisionTower_strictMono barrier)
    (prefixDecisionTower_range_succ_subset barrier)

/-- Every finite stem is decided on a suitable tail of one common increasing
diagonal sequence. This is the global fusion invariant extracted from the
countable decision tower. -/
theorem exists_strictMono_every_finite_prefix_decided_on_tail
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop) :
    ∃ diagonal : ℕ → ℕ, StrictMono diagonal ∧
      ∀ {length : ℕ} (stem : Fin length → ℕ),
        ∃ k : ℕ,
          PrefixAccepts barrier stem (fun n ↦ diagonal (k + n)) ∨
            PrefixRejects barrier stem (fun n ↦ diagonal (k + n)) := by
  obtain ⟨diagonal, hdiagonal, htailFactors⟩ :=
    exists_prefixDecisionDiagonal barrier
  refine ⟨diagonal, hdiagonal, ?_⟩
  intro length stem
  obtain ⟨code, hcode⟩ :=
    enumeratedFiniteNatStem_surjective ⟨length, stem⟩
  have hdecides := prefixDecisionTower_decides barrier code
  rw [hcode] at hdecides
  change PrefixAccepts barrier stem (prefixDecisionTower barrier (code + 1)) ∨
    PrefixRejects barrier stem (prefixDecisionTower barrier (code + 1))
      at hdecides
  obtain ⟨factor, hfactor, htail⟩ := htailFactors (code + 1)
  refine ⟨code + 1, ?_⟩
  obtain haccepts | hrejects := hdecides
  · exact Or.inl <| by
      rw [htail]
      exact haccepts.subsequence hfactor
  · exact Or.inr <| by
      rw [htail]
      exact hrejects.subsequence hfactor


/-- From a cofinal supply of position/cutoff pairs, recursively choose a
strictly increasing sequence whose next position lies beyond the preceding
cutoff. This is the selection skeleton for the strengthened negative Galvin
fusion invariant. -/
theorem exists_strictMono_with_cutoffs_of_cofinal_pairs
    {property : ℕ → ℕ → Prop}
    (hcofinal : ∀ bound : ℕ, ∃ position cutoff : ℕ,
      bound ≤ position ∧ position < cutoff ∧ property position cutoff)
    (start : ℕ) :
    ∃ positions cutoffs : ℕ → ℕ,
      StrictMono positions ∧
        (∀ n, positions n < cutoffs n) ∧
        (∀ n, cutoffs n ≤ positions (n + 1)) ∧
        ∀ n, property (positions n) (cutoffs n) := by
  classical
  choose position cutoff hspec using hcofinal
  let bounds : ℕ → ℕ :=
    fun n ↦ Nat.rec start (fun _ previous ↦ cutoff previous) n
  let positions : ℕ → ℕ := fun n ↦ position (bounds n)
  let cutoffs : ℕ → ℕ := fun n ↦ cutoff (bounds n)
  refine ⟨positions, cutoffs, ?_, ?_, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    exact ((hspec (bounds n)).2.1).trans_le <| by
      change cutoff (bounds n) ≤ position (bounds (n + 1))
      simp only [bounds]
      exact (hspec (cutoff (bounds n))).1
  · intro n
    exact (hspec (bounds n)).2.1
  · intro n
    change cutoff (bounds n) ≤ position (bounds (n + 1))
    simp only [bounds]
    exact (hspec (cutoff (bounds n))).1
  · intro n
    exact (hspec (bounds n)).2.2

/-- Moving the cutoff forward gives a strictly increasing factor between two
ordinary tails of the same sequence. -/
theorem strictMono_tailShift {first second : ℕ} (_h : first ≤ second) :
    StrictMono (fun n ↦ second - first + n) := by
  exact strictMono_nat_of_lt_succ fun n ↦ by omega

/-- A later ordinary tail factors through an earlier one. -/
theorem sequenceTail_comp_tailShift
    (sequence : ℕ → ℕ) {first second : ℕ} (h : first ≤ second) :
    (fun n ↦ sequence (first + n)) ∘
        (fun n ↦ second - first + n) =
      (fun n ↦ sequence (second + n)) := by
  funext n
  simp only [Function.comp_apply]
  congr 1
  omega

/-- Acceptance persists when the cutoff of an ordinary sequence tail is
moved forward. -/
theorem PrefixAccepts.later_tail
    {barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop}
    {stemLength : ℕ} {stem : Fin stemLength → ℕ}
    {sequence : ℕ → ℕ} {first second : ℕ}
    (haccepts : PrefixAccepts barrier stem
      (fun n ↦ sequence (first + n)))
    (h : first ≤ second) :
    PrefixAccepts barrier stem (fun n ↦ sequence (second + n)) := by
  rw [← sequenceTail_comp_tailShift sequence h]
  exact haccepts.subsequence (strictMono_tailShift h)

/-- Hereditary rejection persists when the cutoff of an ordinary sequence
tail is moved forward. -/
theorem PrefixRejects.later_tail
    {barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop}
    {stemLength : ℕ} {stem : Fin stemLength → ℕ}
    {sequence : ℕ → ℕ} {first second : ℕ}
    (hrejects : PrefixRejects barrier stem
      (fun n ↦ sequence (first + n)))
    (h : first ≤ second) :
    PrefixRejects barrier stem (fun n ↦ sequence (second + n)) := by
  rw [← sequenceTail_comp_tailShift sequence h]
  exact hrejects.subsequence (strictMono_tailShift h)

/-- If a one-point extension of a stem is accepted on a tail that contains
the rest of a chosen subsequence, concatenate the accepted extension to
obtain one barrier prefix of that chosen subsequence. -/
theorem exists_barrier_extension_of_prefixAccepts_singleton
    {barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop}
    {stemLength : ℕ} {stem : Fin stemLength → ℕ}
    {first : ℕ} {remaining sequence subsequence factor : ℕ → ℕ}
    (haccepts : PrefixAccepts barrier
      (Fin.append stem (fun _ : Fin 1 ↦ first)) remaining)
    (hfactor : StrictMono factor)
    (hfirst : sequence (subsequence 0) = first)
    (hremainder : ∀ i, remaining (factor i) =
      sequence (subsequence (i + 1))) :
    ∃ extensionLength : ℕ,
      barrier (stemLength + extensionLength)
        (Fin.append stem
          (fun i : Fin extensionLength ↦ sequence (subsequence i))) := by
  obtain ⟨length, hbarrier⟩ := haccepts factor hfactor
  refine ⟨1 + length, ?_⟩
  have hextension :
      (fun i : Fin (1 + length) ↦ sequence (subsequence i)) =
        Fin.append (fun _ : Fin 1 ↦ first)
          (fun i : Fin length ↦ remaining (factor i)) := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · have hj : j = 0 := Fin.eq_zero j
      subst j
      simpa only [Fin.append_left] using hfirst
    · simpa only [Fin.append_right, Fin.val_natAdd, Nat.add_comm] using
        (hremainder j).symm
  rw [Fin.append_assoc, ← hextension] at hbarrier
  convert hbarrier using 1
  · omega
  · have hlength : stemLength + (1 + length) =
        (stemLength + 1) + length := by omega
    rw [Fin.heq_fun_iff hlength]
    intro i
    rfl


/-- Strengthened rejected-extension theorem: beyond one boundary, every
candidate position has a singleton extension rejected on some later tail.
If failures were cofinal, choose accepted position/cutoff pairs recursively;
their sparse diagonal subsequence would accept the original rejected stem. -/
theorem exists_boundary_rejected_singleton_extensions
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    {stemLength : ℕ} (stem : Fin stemLength → ℕ)
    (diagonal : ℕ → ℕ)
    (hdecides : ∀ {length : ℕ} (otherStem : Fin length → ℕ),
      ∃ k : ℕ,
        PrefixAccepts barrier otherStem
            (fun n ↦ diagonal (k + n)) ∨
          PrefixRejects barrier otherStem
            (fun n ↦ diagonal (k + n)))
    {start : ℕ}
    (hrejects : PrefixRejects barrier stem
      (fun n ↦ diagonal (start + n))) :
    ∃ boundary : ℕ, start ≤ boundary ∧
      ∀ position : ℕ, boundary ≤ position →
        ∃ cutoff : ℕ, position < cutoff ∧
          PrefixRejects barrier
            (Fin.append stem (fun _ : Fin 1 ↦ diagonal position))
            (fun n ↦ diagonal (cutoff + n)) := by
  classical
  by_contra hnone
  have hcofinal : ∀ bound : ℕ, ∃ position cutoff : ℕ,
      bound ≤ position ∧ position < cutoff ∧
        (start ≤ position ∧ PrefixAccepts barrier
          (Fin.append stem (fun _ : Fin 1 ↦ diagonal position))
          (fun n ↦ diagonal (cutoff + n))) := by
    intro bound
    let boundary := max start bound
    have hbad : ∃ position : ℕ, boundary ≤ position ∧
        ∀ cutoff : ℕ, position < cutoff →
          ¬ PrefixRejects barrier
            (Fin.append stem (fun _ : Fin 1 ↦ diagonal position))
            (fun n ↦ diagonal (cutoff + n)) := by
      by_contra hbad
      apply hnone
      refine ⟨boundary, le_max_left _ _, ?_⟩
      intro position hposition
      by_contra hnoCutoff
      apply hbad
      refine ⟨position, hposition, ?_⟩
      intro cutoff hpositionCutoff hreject
      apply hnoCutoff
      exact ⟨cutoff, hpositionCutoff, hreject⟩
    obtain ⟨position, hposition, hnoReject⟩ := hbad
    obtain ⟨decisionCutoff, haccepts | hrejects⟩ :=
      hdecides (Fin.append stem (fun _ : Fin 1 ↦ diagonal position))
    · let cutoff := max decisionCutoff (position + 1)
      refine ⟨position, cutoff, le_trans (le_max_right _ _) hposition,
        (Nat.lt_succ_self position).trans_le (le_max_right _ _),
        le_trans (le_max_left _ _) hposition,
        haccepts.later_tail (le_max_left _ _)⟩
    · let cutoff := max decisionCutoff (position + 1)
      have hpositionCutoff : position < cutoff :=
        (Nat.lt_succ_self position).trans_le (le_max_right _ _)
      exfalso
      exact hnoReject cutoff hpositionCutoff
        (hrejects.later_tail (le_max_left _ _))
  obtain ⟨positions, cutoffs, hpositions, _hpositionCutoff,
      hcutoffNext, haccepts⟩ :=
    exists_strictMono_with_cutoffs_of_cofinal_pairs hcofinal start
  let selected : ℕ → ℕ := fun n ↦ diagonal (positions n)
  have hselectedAccepts : PrefixAccepts barrier stem selected := by
    intro subsequence hsubsequence
    let firstIndex : ℕ := subsequence 0
    have haccepts := (haccepts firstIndex).2
    let factor : ℕ → ℕ := fun i ↦
      positions (subsequence (i + 1)) - cutoffs firstIndex
    have hcutoff_le : ∀ i, cutoffs firstIndex ≤
        positions (subsequence (i + 1)) := by
      intro i
      have hindices : firstIndex + 1 ≤ subsequence (i + 1) := by
        exact Nat.succ_le_of_lt <| by
          simpa only [firstIndex, Nat.succ_eq_add_one] using
            hsubsequence (Nat.zero_lt_succ i)
      exact (hcutoffNext firstIndex).trans (hpositions.monotone hindices)
    have hfactor : StrictMono factor := by
      intro i j hij
      apply Nat.sub_lt_sub_right (hcutoff_le i)
      apply hpositions
      apply hsubsequence
      omega
    apply exists_barrier_extension_of_prefixAccepts_singleton
      haccepts hfactor
    · rfl
    · intro i
      dsimp only [factor, firstIndex, selected]
      congr 1
      exact Nat.add_sub_of_le (hcutoff_le i)
  let tailFactor : ℕ → ℕ := fun n ↦ positions n - start
  have htailFactor : StrictMono tailFactor := by
    intro i j hij
    apply Nat.sub_lt_sub_right (haccepts i).1
    exact hpositions hij
  apply hrejects tailFactor htailFactor
  rw [show (fun n ↦ diagonal (start + n)) ∘ tailFactor = selected by
    funext n
    simp only [Function.comp_apply, tailFactor, selected]
    congr 1
    exact Nat.add_sub_of_le (haccepts n).1]
  exact hselectedAccepts

/-- Finitely many stems rejected on one common tail admit a simultaneous
one-point rejected extension. Choose a position beyond the maximum of their
eventual-rejection boundaries, then move the finitely many resulting
rejecting tails to one common later cutoff. -/
theorem exists_common_rejected_singleton_extensions
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    (diagonal : ℕ → ℕ)
    (hdecides : ∀ {length : ℕ} (otherStem : Fin length → ℕ),
      ∃ k : ℕ,
        PrefixAccepts barrier otherStem
            (fun n ↦ diagonal (k + n)) ∨
          PrefixRejects barrier otherStem
            (fun n ↦ diagonal (k + n)))
    (count : ℕ) (stemLength : Fin count → ℕ)
    (stem : ∀ i : Fin count, Fin (stemLength i) → ℕ)
    {start : ℕ}
    (hrejects : ∀ i : Fin count, PrefixRejects barrier (stem i)
      (fun n ↦ diagonal (start + n))) :
    ∃ position cutoff : ℕ,
      start ≤ position ∧ position < cutoff ∧
        ∀ i : Fin count,
          PrefixRejects barrier
            (Fin.append (stem i) (fun _ : Fin 1 ↦ diagonal position))
            (fun n ↦ diagonal (cutoff + n)) := by
  classical
  have heventual : ∀ i : Fin count, ∃ boundary : ℕ,
      start ≤ boundary ∧
        ∀ position : ℕ, boundary ≤ position →
          ∃ cutoff : ℕ, position < cutoff ∧
            PrefixRejects barrier
              (Fin.append (stem i)
                (fun _ : Fin 1 ↦ diagonal position))
              (fun n ↦ diagonal (cutoff + n)) := by
    intro i
    exact exists_boundary_rejected_singleton_extensions barrier
      (stem i) diagonal hdecides (hrejects i)
  let boundaryOf : Fin count → ℕ :=
    fun i ↦ Classical.choose (heventual i)
  have hboundaryOf : ∀ i : Fin count,
      start ≤ boundaryOf i ∧
        ∀ position : ℕ, boundaryOf i ≤ position →
          ∃ cutoff : ℕ, position < cutoff ∧
            PrefixRejects barrier
              (Fin.append (stem i)
                (fun _ : Fin 1 ↦ diagonal position))
              (fun n ↦ diagonal (cutoff + n)) := by
    intro i
    exact Classical.choose_spec (heventual i)
  let position : ℕ := max start (Finset.univ.sup boundaryOf)
  have hpositionStart : start ≤ position := le_max_left _ _
  have hpositionBoundary : ∀ i : Fin count, boundaryOf i ≤ position := by
    intro i
    exact (Finset.le_sup (f := boundaryOf) (Finset.mem_univ i)).trans
      (le_max_right _ _)
  have hcutoffExists : ∀ i : Fin count, ∃ cutoff : ℕ,
      position < cutoff ∧
        PrefixRejects barrier
          (Fin.append (stem i) (fun _ : Fin 1 ↦ diagonal position))
          (fun n ↦ diagonal (cutoff + n)) := by
    intro i
    exact (hboundaryOf i).2 position (hpositionBoundary i)
  let cutoffOf : Fin count → ℕ :=
    fun i ↦ Classical.choose (hcutoffExists i)
  have hcutoffOf : ∀ i : Fin count,
      position < cutoffOf i ∧
        PrefixRejects barrier
          (Fin.append (stem i) (fun _ : Fin 1 ↦ diagonal position))
          (fun n ↦ diagonal (cutoffOf i + n)) := by
    intro i
    exact Classical.choose_spec (hcutoffExists i)
  let cutoff : ℕ := max (position + 1) (Finset.univ.sup cutoffOf)
  refine ⟨position, cutoff, hpositionStart, ?_, ?_⟩
  · exact (Nat.lt_succ_self position).trans_le (le_max_left _ _)
  · intro i
    exact (hcutoffOf i).2.later_tail <|
      (Finset.le_sup (f := cutoffOf) (Finset.mem_univ i)).trans
        (le_max_right _ _)

/-- The finite number of order-preserving sub-stems of a position stem. A
sub-stem is represented by the finite subset of positions that it retains. -/
def finiteSubstemCount (length : ℕ) : ℕ :=
  Fintype.card (Finset (Fin length))

/-- A finite enumeration of all subsets of `Fin length`, hence of all
order-preserving sub-stems of a length-`length` position stem. -/
noncomputable def enumeratedFiniteSubstem (length : ℕ) :
    Fin (finiteSubstemCount length) → Finset (Fin length) :=
  (Fintype.equivFin (Finset (Fin length))).symm

/-- Every finite subset, and therefore every order-preserving sub-stem,
occurs in `enumeratedFiniteSubstem`. -/
theorem enumeratedFiniteSubstem_surjective (length : ℕ) :
    Function.Surjective (enumeratedFiniteSubstem length) := by
  exact (Fintype.equivFin (Finset (Fin length))).symm.surjective

/-- Restrict a finite position stem to a finite subset, listed in increasing
order. -/
def selectedSubstem {length : ℕ} (positions : Fin length → ℕ)
    (subset : Finset (Fin length)) : Fin subset.card → ℕ :=
  fun i ↦ positions (subset.orderEmbOfFin rfl i)


/-- Every subset of `Fin (length + 1)` is uniquely of one of the two forms
needed by fusion: a lifted old subset, or a lifted old subset together with
the new last position. Only existence is needed downstream. -/
theorem exists_finset_castSucc_decomposition
    {length : ℕ} (subset : Finset (Fin (length + 1))) :
    ∃ oldSubset : Finset (Fin length),
      subset = oldSubset.map Fin.castSuccEmb ∨
        subset = insert (Fin.last length)
          (oldSubset.map Fin.castSuccEmb) := by
  classical
  let oldSubset : Finset (Fin length) :=
    subset.preimage Fin.castSucc (Fin.castSucc_injective length).injOn
  have hmem : ∀ i : Fin (length + 1),
      i ∈ oldSubset.map Fin.castSuccEmb ↔
        i ∈ subset ∧ i ≠ Fin.last length := by
    intro i
    constructor
    · intro hi
      simp only [Finset.mem_map] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      exact ⟨Finset.mem_preimage.mp hj, Fin.castSucc_ne_last j⟩
    · rintro ⟨hi, hiLast⟩
      have hiLt : (i : ℕ) < length := by
        by_contra hnot
        have hiVal : (i : ℕ) = length := by omega
        apply hiLast
        exact Fin.ext hiVal
      let j : Fin length := ⟨i, hiLt⟩
      have hj : j.castSucc = i := Fin.ext rfl
      refine Finset.mem_map.mpr ⟨j, ?_, hj⟩
      exact Finset.mem_preimage.mpr <| by simpa only [hj] using hi
  refine ⟨oldSubset, ?_⟩
  by_cases hlast : Fin.last length ∈ subset
  · apply Or.inr
    ext i
    rw [Finset.mem_insert, hmem]
    constructor
    · intro hi
      by_cases hiLast : i = Fin.last length
      · exact Or.inl hiLast
      · exact Or.inr ⟨hi, hiLast⟩
    · rintro (rfl | ⟨hi, _⟩)
      · exact hlast
      · exact hi
  · apply Or.inl
    ext i
    rw [hmem]
    constructor
    · intro hi
      exact ⟨hi, fun hiLast ↦ hlast (hiLast ▸ hi)⟩
    · exact fun hi ↦ hi.1

/-- Lifting an old subset through `Fin.castSucc` does not change its selected
sub-stem when the ambient position stem is extended at the end. The result is
heterogeneous only because `Finset.card_map` is propositional. -/
theorem selectedSubstem_map_castSucc_heq
    {length : ℕ} (positions : Fin length → ℕ) (last : ℕ)
    (subset : Finset (Fin length)) :
    HEq
      (selectedSubstem
        (Fin.append positions (fun _ : Fin 1 ↦ last))
        (subset.map Fin.castSuccEmb))
      (selectedSubstem positions subset) := by
  classical
  let lifted : Finset (Fin (length + 1)) :=
    subset.map Fin.castSuccEmb
  have hcard : lifted.card = subset.card := by
    simp only [lifted, Finset.card_map]
  have hemb :
      (fun i : Fin subset.card ↦
        (subset.orderEmbOfFin rfl i).castSucc) =
        lifted.orderEmbOfFin hcard := by
    apply Finset.orderEmbOfFin_unique hcard
    · intro i
      simp only [lifted, Finset.mem_map]
      exact ⟨subset.orderEmbOfFin rfl i,
        subset.orderEmbOfFin_mem rfl i, rfl⟩
    · exact Fin.strictMono_castSucc.comp
        (subset.orderEmbOfFin rfl).strictMono
  rw [Fin.heq_fun_iff hcard]
  intro i
  let j : Fin subset.card := Fin.cast hcard i
  change Fin.append positions (fun _ : Fin 1 ↦ last)
      (lifted.orderEmbOfFin rfl i) =
    positions (subset.orderEmbOfFin rfl j)
  have hi := congrFun hemb j
  have hij : lifted.orderEmbOfFin rfl i =
      (subset.orderEmbOfFin rfl j).castSucc := by
    simpa only [j] using hi.symm
  rw [hij]
  have hcast : (subset.orderEmbOfFin rfl j).castSucc =
      Fin.castAdd 1 (subset.orderEmbOfFin rfl j) := Fin.ext rfl
  rw [hcast, Fin.append_left]

/-- Inserting the new last index after lifting an old subset selects exactly
the old sub-stem followed by the newly appended position. -/
theorem selectedSubstem_insert_last_map_castSucc_heq
    {length : ℕ} (positions : Fin length → ℕ) (last : ℕ)
    (subset : Finset (Fin length)) :
    HEq
      (selectedSubstem
        (Fin.append positions (fun _ : Fin 1 ↦ last))
        (insert (Fin.last length) (subset.map Fin.castSuccEmb)))
      (Fin.append (selectedSubstem positions subset)
        (fun _ : Fin 1 ↦ last)) := by
  classical
  let lifted : Finset (Fin (length + 1)) :=
    subset.map Fin.castSuccEmb
  let withLast : Finset (Fin (length + 1)) :=
    insert (Fin.last length) lifted
  have hlastNotMem : Fin.last length ∉ lifted := by
    simp only [lifted, Finset.mem_map]
    rintro ⟨i, _, hi⟩
    exact Fin.castSucc_ne_last i hi
  have hcard : withLast.card = subset.card + 1 := by
    simp only [withLast, Finset.card_insert_of_notMem hlastNotMem,
      lifted, Finset.card_map]
  let candidate : Fin (subset.card + 1) → Fin (length + 1) :=
    Fin.append
      (fun i ↦ (subset.orderEmbOfFin rfl i).castSucc)
      (fun _ : Fin 1 ↦ Fin.last length)
  have hcandidateStrict : StrictMono candidate := by
    intro i j hij
    by_cases hj : (j : ℕ) < subset.card
    · let i' : Fin subset.card := ⟨i, lt_trans hij hj⟩
      let j' : Fin subset.card := ⟨j, hj⟩
      have hi : i = Fin.castAdd 1 i' := Fin.ext rfl
      have hj' : j = Fin.castAdd 1 j' := Fin.ext rfl
      rw [hi, hj']
      simp only [candidate, Fin.append_left]
      exact Fin.strictMono_castSucc
        ((subset.orderEmbOfFin rfl).strictMono hij)
    · have hjval : (j : ℕ) = subset.card := by omega
      let i' : Fin subset.card := ⟨i, by omega⟩
      have hi : i = Fin.castAdd 1 i' := Fin.ext rfl
      have hj' : j = Fin.natAdd subset.card (0 : Fin 1) := Fin.ext <| by
        simp only [Fin.val_natAdd, Fin.val_zero, Nat.add_zero]
        exact hjval
      rw [hi, hj']
      simp only [candidate, Fin.append_left, Fin.append_right]
      exact Fin.castSucc_lt_last _
  have hemb : candidate = withLast.orderEmbOfFin hcard := by
    apply Finset.orderEmbOfFin_unique hcard
    · intro i
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
      · simp only [candidate, Fin.append_left, withLast,
          Finset.mem_insert]
        exact Or.inr <| by
          simp only [lifted, Finset.mem_map]
          exact ⟨subset.orderEmbOfFin rfl j,
            subset.orderEmbOfFin_mem rfl j, rfl⟩
      · simp only [candidate, Fin.append_right, withLast,
          Finset.mem_insert, true_or]
    · exact hcandidateStrict
  rw [Fin.heq_fun_iff hcard]
  intro i
  let j : Fin (subset.card + 1) := Fin.cast hcard i
  change Fin.append positions (fun _ : Fin 1 ↦ last)
      (withLast.orderEmbOfFin rfl i) =
    Fin.append (selectedSubstem positions subset)
      (fun _ : Fin 1 ↦ last) j
  have hi := congrFun hemb j
  have hij : withLast.orderEmbOfFin rfl i = candidate j := by
    simpa only [j] using hi.symm
  rw [hij]
  refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j
  · simp only [candidate, Fin.append_left, selectedSubstem]
    have hcast : (subset.orderEmbOfFin rfl k).castSucc =
        Fin.castAdd 1 (subset.orderEmbOfFin rfl k) := Fin.ext rfl
    rw [hcast, Fin.append_left]
  · simp only [candidate, Fin.append_right]
    have hlast : Fin.last length =
        Fin.natAdd length (0 : Fin 1) := Fin.ext <| by
      simp only [Fin.val_last, Fin.val_natAdd, Fin.val_zero, Nat.add_zero]
    rw [hlast, Fin.append_right]

/-- If every sub-stem of a finite selected position set is rejected on one
tail, one new position and one later cutoff reject the singleton extension
of every such sub-stem simultaneously. This is the finite family needed by
the corrected negative Galvin fusion. -/
theorem exists_common_rejected_singleton_extensions_of_selectedSubstems
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    (diagonal : ℕ → ℕ)
    (hdecides : ∀ {length : ℕ} (otherStem : Fin length → ℕ),
      ∃ k : ℕ,
        PrefixAccepts barrier otherStem
            (fun n ↦ diagonal (k + n)) ∨
          PrefixRejects barrier otherStem
            (fun n ↦ diagonal (k + n)))
    {length : ℕ} (positions : Fin length → ℕ) {start : ℕ}
    (hrejects : ∀ subset : Finset (Fin length),
      PrefixRejects barrier
        (fun i ↦ diagonal (selectedSubstem positions subset i))
        (fun n ↦ diagonal (start + n))) :
    ∃ position cutoff : ℕ,
      start ≤ position ∧ position < cutoff ∧
        ∀ subset : Finset (Fin length),
          PrefixRejects barrier
            (Fin.append
              (fun i ↦ diagonal (selectedSubstem positions subset i))
              (fun _ : Fin 1 ↦ diagonal position))
            (fun n ↦ diagonal (cutoff + n)) := by
  classical
  obtain ⟨position, cutoff, hposition, hpositionCutoff, hcommon⟩ :=
    exists_common_rejected_singleton_extensions barrier diagonal hdecides
      (finiteSubstemCount length)
      (fun code ↦ (enumeratedFiniteSubstem length code).card)
      (fun code i ↦ diagonal
        (selectedSubstem positions (enumeratedFiniteSubstem length code) i))
      (fun code ↦ hrejects (enumeratedFiniteSubstem length code))
  refine ⟨position, cutoff, hposition, hpositionCutoff, ?_⟩
  intro subset
  obtain ⟨code, rfl⟩ := enumeratedFiniteSubstem_surjective length subset
  exact hcommon code

/-- Appending one value beyond a common cutoff preserves strict increase of a
finite natural-number stem. -/
theorem strictMono_fin_append_singleton
    {length cutoff last : ℕ} {values : Fin length → ℕ}
    (hvalues : StrictMono values)
    (hbefore : ∀ i, values i < cutoff)
    (hcutoff : cutoff ≤ last) :
    StrictMono (Fin.append values (fun _ : Fin 1 ↦ last)) := by
  intro i j hij
  by_cases hj : (j : ℕ) < length
  · let i' : Fin length := ⟨i, lt_trans hij hj⟩
    let j' : Fin length := ⟨j, hj⟩
    have hi : i = Fin.castAdd 1 i' := Fin.ext rfl
    have hj' : j = Fin.castAdd 1 j' := Fin.ext rfl
    rw [hi, hj', Fin.append_left, Fin.append_left]
    exact hvalues hij
  · have hjval : (j : ℕ) = length := by omega
    let i' : Fin length := ⟨i, by omega⟩
    have hi : i = Fin.castAdd 1 i' := Fin.ext rfl
    have hj' : j = Fin.natAdd length (0 : Fin 1) := Fin.ext <| by
      simp only [Fin.val_natAdd, Fin.val_zero, Nat.add_zero]
      exact hjval
    rw [hi, hj', Fin.append_left, Fin.append_right]
    exact (hbefore i').trans_le hcutoff

/-- The dependent invariant for the recursively constructed negative Galvin
branch: a strictly increasing finite position stem lies before `cutoff`, and
its image under the globally deciding diagonal is rejected on that tail. -/
structure RejectedFusionState
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    (diagonal : ℕ → ℕ) (length : ℕ) where
  positions : Fin length → ℕ
  cutoff : ℕ
  strictMono_positions : StrictMono positions
  positions_lt_cutoff : ∀ i, positions i < cutoff
  rejects : PrefixRejects barrier
    (fun i ↦ diagonal (positions i))
    (fun n ↦ diagonal (cutoff + n))

/-- A rejected empty stem supplies the initial negative-branch fusion
state. -/
def initialRejectedFusionState
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    (diagonal : ℕ → ℕ) (start : ℕ)
    (hrejects : PrefixRejects barrier (Fin.elim0 : Fin 0 → ℕ)
      (fun n ↦ diagonal (start + n))) :
    RejectedFusionState barrier diagonal 0 where
  positions := Fin.elim0
  cutoff := start
  strictMono_positions := fun i ↦ Fin.elim0 i
  positions_lt_cutoff := fun i ↦ Fin.elim0 i
  rejects := hrejects


/-- The corrected dependent invariant for the negative Galvin branch. Every
order-preserving sub-stem of the selected positions, not merely the full
prefix, is rejected on one common tail. -/
structure AllSubstemsRejectedFusionState
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    (diagonal : ℕ → ℕ) (length : ℕ) where
  positions : Fin length → ℕ
  cutoff : ℕ
  strictMono_positions : StrictMono positions
  positions_lt_cutoff : ∀ i, positions i < cutoff
  rejects_substems : ∀ subset : Finset (Fin length),
    PrefixRejects barrier
      (fun i ↦ diagonal (selectedSubstem positions subset i))
      (fun n ↦ diagonal (cutoff + n))

/-- A rejected empty stem supplies the initial corrected fusion state. Its
only finite sub-stem is again the empty stem. -/
def initialAllSubstemsRejectedFusionState
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    (diagonal : ℕ → ℕ) (start : ℕ)
    (hrejects : PrefixRejects barrier (Fin.elim0 : Fin 0 → ℕ)
      (fun n ↦ diagonal (start + n))) :
    AllSubstemsRejectedFusionState barrier diagonal 0 where
  positions := Fin.elim0
  cutoff := start
  strictMono_positions := fun i ↦ Fin.elim0 i
  positions_lt_cutoff := fun i ↦ Fin.elim0 i
  rejects_substems := by
    intro subset
    have hsubset : subset = ∅ := by
      ext i
      exact Fin.elim0 i
    subst subset
    convert hrejects using 1
    funext i
    exact Fin.elim0 i

/-- Coherence relation for corrected fusion states: all old positions are
preserved and the new last position lies beyond the old cutoff. -/
def AllSubstemsRejectedFusionState.Extends
    {barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop}
    {diagonal : ℕ → ℕ} {length : ℕ}
    (current : AllSubstemsRejectedFusionState barrier diagonal length)
    (next : AllSubstemsRejectedFusionState barrier diagonal (length + 1)) :
    Prop :=
  (∀ i : Fin length, next.positions i.castSucc = current.positions i) ∧
    current.cutoff ≤ next.positions (Fin.last length)

/-- The simultaneous rejected-extension theorem advances the corrected
fusion invariant by one coherent selected position. New sub-stems omitting
the point inherit old rejection on the later tail; those containing it use
the simultaneous singleton-extension rejection. -/
theorem exists_nextAllSubstemsRejectedFusionState
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    (diagonal : ℕ → ℕ)
    (hdecides : ∀ {length : ℕ} (stem : Fin length → ℕ),
      ∃ k : ℕ,
        PrefixAccepts barrier stem (fun n ↦ diagonal (k + n)) ∨
          PrefixRejects barrier stem (fun n ↦ diagonal (k + n)))
    {length : ℕ}
    (current : AllSubstemsRejectedFusionState barrier diagonal length) :
    ∃ next : AllSubstemsRejectedFusionState barrier diagonal (length + 1),
      current.Extends next := by
  classical
  obtain ⟨position, nextCutoff, hposition, hpositionCutoff, hrejects⟩ :=
    exists_common_rejected_singleton_extensions_of_selectedSubstems
      barrier diagonal hdecides current.positions current.rejects_substems
  let nextPositions : Fin (length + 1) → ℕ :=
    Fin.append current.positions (fun _ : Fin 1 ↦ position)
  have hnextStrict : StrictMono nextPositions :=
    strictMono_fin_append_singleton current.strictMono_positions
      current.positions_lt_cutoff hposition
  have hnextBefore : ∀ i, nextPositions i < nextCutoff := by
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [nextPositions, Fin.append_left]
      exact ((current.positions_lt_cutoff j).trans_le hposition).trans
        hpositionCutoff
    · have hj : j = 0 := Fin.eq_zero j
      subst j
      simpa only [nextPositions, Fin.append_right] using hpositionCutoff
  let next : AllSubstemsRejectedFusionState barrier diagonal (length + 1) :=
    { positions := nextPositions
      cutoff := nextCutoff
      strictMono_positions := hnextStrict
      positions_lt_cutoff := hnextBefore
      rejects_substems := by
        intro subset
        obtain ⟨oldSubset, homit | hinclude⟩ :=
          exists_finset_castSucc_decomposition subset
        · subst subset
          have hold := (current.rejects_substems oldSubset).later_tail
            (hposition.trans hpositionCutoff.le)
          have hselected := selectedSubstem_map_castSucc_heq
            current.positions position oldSubset
          change PrefixRejects barrier
            (fun i ↦ diagonal
              (selectedSubstem nextPositions
                (oldSubset.map Fin.castSuccEmb) i))
            (fun n ↦ diagonal (nextCutoff + n))
          dsimp only [nextPositions]
          have hcard : oldSubset.card =
              (oldSubset.map Fin.castSuccEmb).card := by
            simp only [Finset.card_map]
          have hmapped : HEq
              (fun i ↦ diagonal
                (selectedSubstem current.positions oldSubset i))
              (fun i ↦ diagonal
                (selectedSubstem
                  (Fin.append current.positions
                    (fun _ : Fin 1 ↦ position))
                  (oldSubset.map Fin.castSuccEmb) i)) := by
            apply (Fin.heq_fun_iff hcard).2
            intro i
            exact congrArg diagonal <|
              (Fin.heq_fun_iff hcard).1 hselected.symm i
          exact hold.congr_heq hcard hmapped
        · subst subset
          have hselected :=
            selectedSubstem_insert_last_map_castSucc_heq
              current.positions position oldSubset
          change PrefixRejects barrier
            (fun i ↦ diagonal
              (selectedSubstem nextPositions
                (insert (Fin.last length)
                  (oldSubset.map Fin.castSuccEmb)) i))
            (fun n ↦ diagonal (nextCutoff + n))
          dsimp only [nextPositions]
          have hlastNotMem : Fin.last length ∉
              oldSubset.map Fin.castSuccEmb := by
            simp only [Finset.mem_map]
            rintro ⟨i, _, hi⟩
            exact Fin.castSucc_ne_last i hi
          have hcard : oldSubset.card + 1 =
              (insert (Fin.last length)
                (oldSubset.map Fin.castSuccEmb)).card := by
            simp only [Finset.card_insert_of_notMem hlastNotMem,
              Finset.card_map]
          have hmapped : HEq
              (fun i ↦ diagonal
                (Fin.append (selectedSubstem current.positions oldSubset)
                  (fun _ : Fin 1 ↦ position) i))
              (fun i ↦ diagonal
                (selectedSubstem
                  (Fin.append current.positions
                    (fun _ : Fin 1 ↦ position))
                  (insert (Fin.last length)
                    (oldSubset.map Fin.castSuccEmb)) i)) := by
            apply (Fin.heq_fun_iff hcard).2
            intro i
            exact congrArg diagonal <|
              (Fin.heq_fun_iff hcard).1 hselected.symm i
          have happend :
              (fun i ↦ diagonal
                (Fin.append (selectedSubstem current.positions oldSubset)
                  (fun _ : Fin 1 ↦ position) i)) =
                Fin.append
                  (fun i ↦ diagonal
                    (selectedSubstem current.positions oldSubset i))
                  (fun _ : Fin 1 ↦ diagonal position) := by
            funext i
            refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
            · simp only [Fin.append_left]
            · simp only [Fin.append_right]
          exact (hrejects oldSubset).congr_heq hcard <|
            (heq_of_eq happend.symm).trans hmapped }
  refine ⟨next, ?_, ?_⟩
  · intro i
    change Fin.append current.positions (fun _ : Fin 1 ↦ position)
      i.castSucc = current.positions i
    have hi : i.castSucc = Fin.castAdd 1 i := Fin.ext rfl
    rw [hi, Fin.append_left]
  · simp only [next, nextPositions]
    have hlast : Fin.last length =
        Fin.natAdd length (0 : Fin 1) := Fin.ext <| by
      simp only [Fin.val_last, Fin.val_natAdd, Fin.val_zero, Nat.add_zero]
    rw [hlast, Fin.append_right]
    exact hposition

/-- Choose the canonical corrected successor supplied by the existence
theorem. -/
noncomputable def nextAllSubstemsRejectedFusionState
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    (diagonal : ℕ → ℕ)
    (hdecides : ∀ {length : ℕ} (stem : Fin length → ℕ),
      ∃ k : ℕ,
        PrefixAccepts barrier stem (fun n ↦ diagonal (k + n)) ∨
          PrefixRejects barrier stem (fun n ↦ diagonal (k + n)))
    {length : ℕ}
    (current : AllSubstemsRejectedFusionState barrier diagonal length) :
    AllSubstemsRejectedFusionState barrier diagonal (length + 1) :=
  Classical.choose
    (exists_nextAllSubstemsRejectedFusionState
      barrier diagonal hdecides current)

/-- The chosen corrected successor coherently extends its predecessor. -/
theorem nextAllSubstemsRejectedFusionState_extends
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    (diagonal : ℕ → ℕ)
    (hdecides : ∀ {length : ℕ} (stem : Fin length → ℕ),
      ∃ k : ℕ,
        PrefixAccepts barrier stem (fun n ↦ diagonal (k + n)) ∨
          PrefixRejects barrier stem (fun n ↦ diagonal (k + n)))
    {length : ℕ}
    (current : AllSubstemsRejectedFusionState barrier diagonal length) :
    current.Extends
      (nextAllSubstemsRejectedFusionState
        barrier diagonal hdecides current) :=
  Classical.choose_spec
    (exists_nextAllSubstemsRejectedFusionState
      barrier diagonal hdecides current)

/-- Iterate corrected fusion from a rejected empty stem. Stage `length`
contains exactly `length` selected positions. -/
noncomputable def allSubstemsRejectedFusionStates
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    (diagonal : ℕ → ℕ)
    (hdecides : ∀ {length : ℕ} (stem : Fin length → ℕ),
      ∃ k : ℕ,
        PrefixAccepts barrier stem (fun n ↦ diagonal (k + n)) ∨
          PrefixRejects barrier stem (fun n ↦ diagonal (k + n)))
    (start : ℕ)
    (hrejects : PrefixRejects barrier (Fin.elim0 : Fin 0 → ℕ)
      (fun n ↦ diagonal (start + n))) :
    ∀ length : ℕ,
      AllSubstemsRejectedFusionState barrier diagonal length
  | 0 => initialAllSubstemsRejectedFusionState
      barrier diagonal start hrejects
  | length + 1 => nextAllSubstemsRejectedFusionState
      barrier diagonal hdecides
      (allSubstemsRejectedFusionStates
        barrier diagonal hdecides start hrejects length)

/-- Consecutive stages of the corrected fusion sequence satisfy the
coherence relation. -/
theorem allSubstemsRejectedFusionStates_succ_extends
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    (diagonal : ℕ → ℕ)
    (hdecides : ∀ {length : ℕ} (stem : Fin length → ℕ),
      ∃ k : ℕ,
        PrefixAccepts barrier stem (fun n ↦ diagonal (k + n)) ∨
          PrefixRejects barrier stem (fun n ↦ diagonal (k + n)))
    (start : ℕ)
    (hrejects : PrefixRejects barrier (Fin.elim0 : Fin 0 → ℕ)
      (fun n ↦ diagonal (start + n))) (length : ℕ) :
    (allSubstemsRejectedFusionStates
      barrier diagonal hdecides start hrejects length).Extends
      (allSubstemsRejectedFusionStates
        barrier diagonal hdecides start hrejects (length + 1)) := by
  exact nextAllSubstemsRejectedFusionState_extends barrier diagonal hdecides
    (allSubstemsRejectedFusionStates
      barrier diagonal hdecides start hrejects length)

/-- The infinite candidate extracted from corrected fusion: its `n`th entry
is the new last position at stage `n + 1`. -/
noncomputable def allSubstemsRejectedFusionPositions
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    (diagonal : ℕ → ℕ)
    (hdecides : ∀ {length : ℕ} (stem : Fin length → ℕ),
      ∃ k : ℕ,
        PrefixAccepts barrier stem (fun n ↦ diagonal (k + n)) ∨
          PrefixRejects barrier stem (fun n ↦ diagonal (k + n)))
    (start : ℕ)
    (hrejects : PrefixRejects barrier (Fin.elim0 : Fin 0 → ℕ)
      (fun n ↦ diagonal (start + n))) (n : ℕ) : ℕ :=
  (allSubstemsRejectedFusionStates
    barrier diagonal hdecides start hrejects (n + 1)).positions (Fin.last n)

/-- The positions extracted from corrected fusion are strictly increasing. -/
theorem allSubstemsRejectedFusionPositions_strictMono
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    (diagonal : ℕ → ℕ)
    (hdecides : ∀ {length : ℕ} (stem : Fin length → ℕ),
      ∃ k : ℕ,
        PrefixAccepts barrier stem (fun n ↦ diagonal (k + n)) ∨
          PrefixRejects barrier stem (fun n ↦ diagonal (k + n)))
    (start : ℕ)
    (hrejects : PrefixRejects barrier (Fin.elim0 : Fin 0 → ℕ)
      (fun n ↦ diagonal (start + n))) :
    StrictMono (allSubstemsRejectedFusionPositions
      barrier diagonal hdecides start hrejects) := by
  apply strictMono_nat_of_lt_succ
  intro n
  let current := allSubstemsRejectedFusionStates
    barrier diagonal hdecides start hrejects (n + 1)
  have hextends := allSubstemsRejectedFusionStates_succ_extends
    barrier diagonal hdecides start hrejects (n + 1)
  change current.positions (Fin.last n) <
    (allSubstemsRejectedFusionStates
      barrier diagonal hdecides start hrejects (n + 1 + 1)).positions
        (Fin.last (n + 1))
  exact (current.positions_lt_cutoff (Fin.last n)).trans_le hextends.2

/-- The first `length` entries of the extracted infinite position sequence
are exactly the positions stored at fusion stage `length`. -/
theorem allSubstemsRejectedFusionPositions_eq_state_positions
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    (diagonal : ℕ → ℕ)
    (hdecides : ∀ {length : ℕ} (stem : Fin length → ℕ),
      ∃ k : ℕ,
        PrefixAccepts barrier stem (fun n ↦ diagonal (k + n)) ∨
          PrefixRejects barrier stem (fun n ↦ diagonal (k + n)))
    (start : ℕ)
    (hrejects : PrefixRejects barrier (Fin.elim0 : Fin 0 → ℕ)
      (fun n ↦ diagonal (start + n))) :
    ∀ (length : ℕ) (i : Fin length),
      allSubstemsRejectedFusionPositions
          barrier diagonal hdecides start hrejects i =
        (allSubstemsRejectedFusionStates
          barrier diagonal hdecides start hrejects length).positions i := by
  intro length
  induction length with
  | zero =>
      exact fun i ↦ Fin.elim0 i
  | succ length ih =>
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · rfl
      · change allSubstemsRejectedFusionPositions
          barrier diagonal hdecides start hrejects j =
          (allSubstemsRejectedFusionStates
            barrier diagonal hdecides start hrejects (length + 1)).positions
              j.castSucc
        rw [ih j]
        exact (allSubstemsRejectedFusionStates_succ_extends
          barrier diagonal hdecides start hrejects length).1 j |>.symm

/-- Every finite increasing selection from the extracted infinite sequence is
represented by a subset-selected sub-stem of one sufficiently late fusion
state. The heterogeneous equality records the finset cardinality proof. -/
theorem exists_state_selectedSubstem_heq_finite_selection
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    (diagonal : ℕ → ℕ)
    (hdecides : ∀ {length : ℕ} (stem : Fin length → ℕ),
      ∃ k : ℕ,
        PrefixAccepts barrier stem (fun n ↦ diagonal (k + n)) ∨
          PrefixRejects barrier stem (fun n ↦ diagonal (k + n)))
    (start : ℕ)
    (hrejects : PrefixRejects barrier (Fin.elim0 : Fin 0 → ℕ)
      (fun n ↦ diagonal (start + n)))
    (count : ℕ) (indices : Fin count → ℕ)
    (hindices : StrictMono indices) :
    ∃ (stage : ℕ) (subset : Finset (Fin stage)),
      subset.card = count ∧
        HEq
          (selectedSubstem
            (allSubstemsRejectedFusionStates
              barrier diagonal hdecides start hrejects stage).positions subset)
          (fun i ↦ allSubstemsRejectedFusionPositions
            barrier diagonal hdecides start hrejects (indices i)) := by
  classical
  let stage : ℕ := Finset.univ.sup indices + 1
  have hbounded : ∀ i : Fin count, indices i < stage := by
    intro i
    exact Nat.lt_succ_of_le <|
      Finset.le_sup (f := indices) (Finset.mem_univ i)
  let boundedIndices : Fin count ↪o Fin stage :=
    OrderEmbedding.ofStrictMono (fun i ↦ ⟨indices i, hbounded i⟩) <| by
      intro i j hij
      exact hindices hij
  let subset : Finset (Fin stage) :=
    Finset.univ.map boundedIndices.toEmbedding
  have hcard : subset.card = count := by
    simp only [subset, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hemb : (fun i : Fin count ↦ boundedIndices i) =
      subset.orderEmbOfFin hcard := by
    apply Finset.orderEmbOfFin_unique hcard
    · intro i
      simp only [subset, Finset.mem_map, Finset.mem_univ, true_and]
      exact ⟨i, rfl⟩
    · exact boundedIndices.strictMono
  refine ⟨stage, subset, hcard, ?_⟩
  rw [Fin.heq_fun_iff hcard]
  intro i
  let j : Fin count := Fin.cast hcard i
  change
    (allSubstemsRejectedFusionStates
      barrier diagonal hdecides start hrejects stage).positions
        (subset.orderEmbOfFin rfl i) =
      allSubstemsRejectedFusionPositions
        barrier diagonal hdecides start hrejects (indices j)
  have hi := congrFun hemb j
  have hij : subset.orderEmbOfFin rfl i = boundedIndices j := by
    simpa only [j] using hi.symm
  rw [hij]
  exact (allSubstemsRejectedFusionPositions_eq_state_positions
    barrier diagonal hdecides start hrejects stage (boundedIndices j)).symm

/-- A rejected empty stem on the globally deciding diagonal yields the
negative homogeneous branch of Galvin's open-prefix lemma. Any alleged
barrier prefix of a subsequence is represented by a rejected state sub-stem,
but a barrier stem is accepted on every tail. -/
theorem exists_strictMono_avoids_barrier_of_empty_prefixRejects
    (barrier : ∀ length : ℕ, (Fin length → ℕ) → Prop)
    (diagonal : ℕ → ℕ) (hdiagonal : StrictMono diagonal)
    (hdecides : ∀ {length : ℕ} (stem : Fin length → ℕ),
      ∃ k : ℕ,
        PrefixAccepts barrier stem (fun n ↦ diagonal (k + n)) ∨
          PrefixRejects barrier stem (fun n ↦ diagonal (k + n)))
    {start : ℕ}
    (hrejects : PrefixRejects barrier (Fin.elim0 : Fin 0 → ℕ)
      (fun n ↦ diagonal (start + n))) :
    ∃ base : ℕ → ℕ, StrictMono base ∧
      ∀ subsequence : ℕ → ℕ, StrictMono subsequence →
        ∀ length : ℕ,
          ¬ barrier length (fun i ↦ base (subsequence i)) := by
  classical
  let positions := allSubstemsRejectedFusionPositions
    barrier diagonal hdecides start hrejects
  let base : ℕ → ℕ := fun n ↦ diagonal (positions n)
  have hpositions : StrictMono positions :=
    allSubstemsRejectedFusionPositions_strictMono
      barrier diagonal hdecides start hrejects
  refine ⟨base, hdiagonal.comp hpositions, ?_⟩
  intro subsequence hsubsequence length hbarrier
  let indices : Fin length → ℕ := fun i ↦ subsequence i
  have hindices : StrictMono indices := by
    intro i j hij
    exact hsubsequence hij
  obtain ⟨stage, subset, hcard, hselected⟩ :=
    exists_state_selectedSubstem_heq_finite_selection
      barrier diagonal hdecides start hrejects length indices hindices
  let state := allSubstemsRejectedFusionStates
    barrier diagonal hdecides start hrejects stage
  have hmapped : HEq
      (fun i ↦ diagonal (selectedSubstem state.positions subset i))
      (fun i ↦ diagonal (positions (indices i))) := by
    apply (Fin.heq_fun_iff hcard).2
    intro i
    exact congrArg diagonal <|
      (Fin.heq_fun_iff hcard).1 hselected i
  have htargetRejects : PrefixRejects barrier
      (fun i ↦ diagonal (positions (indices i)))
      (fun n ↦ diagonal (state.cutoff + n)) :=
    (state.rejects_substems subset).congr_heq hcard hmapped
  apply htargetRejects id strictMono_id
  apply prefixAccepts_of_barrier
  simpa only [base, positions, indices] using hbarrier

/-- Galvin's open-prefix lemma. First fuse once to decide every finite stem
on tails of one increasing diagonal, then inspect the empty stem. Acceptance
gives the hitting branch directly; rejection feeds the corrected all-sub-stem
fusion and gives the avoiding branch. -/
theorem galvinOpenPrefixRamsey : GalvinOpenPrefixRamsey := by
  intro barrier
  obtain ⟨diagonal, hdiagonal, hdecides⟩ :=
    exists_strictMono_every_finite_prefix_decided_on_tail barrier
  obtain ⟨start, haccepts | hrejects⟩ :=
    hdecides (Fin.elim0 : Fin 0 → ℕ)
  · let base : ℕ → ℕ := fun n ↦ diagonal (start + n)
    have hbase : StrictMono base := hdiagonal.comp <|
      strictMono_nat_of_lt_succ fun n ↦ by omega
    refine ⟨base, hbase, Or.inl ?_⟩
    intro subsequence hsubsequence
    obtain ⟨length, hbarrier⟩ := haccepts subsequence hsubsequence
    refine ⟨length, ?_⟩
    convert hbarrier using 1
    · omega
    · rw [Fin.heq_fun_iff (by omega)]
      intro i
      change diagonal (start + subsequence i) =
        Fin.append Fin.elim0
          (fun i ↦ diagonal (start + subsequence i)) ⟨i, by omega⟩
      have hi : (⟨i, by omega⟩ : Fin (0 + length)) =
          Fin.natAdd 0 i := Fin.ext <| by
        simp only [Fin.val_natAdd]
        omega
      rw [hi, Fin.append_right]
  · obtain ⟨base, hbase, havoids⟩ :=
      exists_strictMono_avoids_barrier_of_empty_prefixRejects
        barrier diagonal hdiagonal hdecides hrejects
    exact ⟨base, hbase, Or.inr havoids⟩

/-- The closed-set Galvin--Prikry theorem yields Rosenthal's fixed-threshold
pair dichotomy. In the negative homogeneous branch, a point visiting both
sides frequently would select an alternating subsequence in the closed set.
In the positive branch, a four-place block selector puts any prescribed
finite low/high pattern into even/odd positions of one subsequence. -/
theorem thresholdPairSubsequenceDichotomy_of_galvinPrikry
    (hGalvinPrikry : GalvinPrikryClosedSubsequenceRamsey) :
    ThresholdPairSubsequenceDichotomy.{u} := by
  classical
  intro α values low high _hgap
  let closedSet : Set (ℕ → ℕ) :=
    {indices | AllAlternatingPrefixesRealized values low high indices}
  obtain ⟨base, hbase, hAll | hNone⟩ :=
    hGalvinPrikry closedSet
      (isClosed_allAlternatingPrefixesRealized values low high)
  · let selected : ℕ → ℕ := fun n ↦ base (4 * n + 2)
    have hselected : StrictMono selected := by
      exact hbase.comp <| strictMono_nat_of_lt_succ fun n ↦ by
        omega
    refine ⟨selected, hselected, Or.inr ?_⟩
    intro E F hdisjoint
    let blockSelector : ℕ → ℕ := fun m ↦
      if Even m then
        if m / 2 ∈ F then 4 * (m / 2) + 1 else 4 * (m / 2) + 2
      else
        if m / 2 ∈ F then 4 * (m / 2) + 2 else 4 * (m / 2) + 3
    have hblockSelector : StrictMono blockSelector := by
      apply strictMono_nat_of_lt_succ
      intro m
      obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
      · have hdivEven : (2 * n) / 2 = n := by omega
        have hdivOdd : (2 * n + 1) / 2 = n := by omega
        simp only [blockSelector, even_two_mul, if_true,
          Nat.not_even_two_mul_add_one, if_false, hdivEven, hdivOdd]
        split_ifs <;> omega
      · have hsucc : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
        rw [hsucc]
        have hdivOdd : (2 * n + 1) / 2 = n := by omega
        have hdivEven : (2 * (n + 1)) / 2 = n + 1 := by omega
        simp only [blockSelector, Nat.not_even_two_mul_add_one,
          if_false, even_two_mul, if_true, hdivOdd, hdivEven]
        split_ifs <;> omega
    have hblockEven (n : ℕ) (hn : n ∉ F) :
        blockSelector (2 * n) = 4 * n + 2 := by
      have hdiv : (2 * n) / 2 = n := by omega
      simp only [blockSelector, even_two_mul, if_true, hdiv, hn, if_false]
    have hblockOdd (n : ℕ) (hn : n ∈ F) :
        blockSelector (2 * n + 1) = 4 * n + 2 := by
      have hdiv : (2 * n + 1) / 2 = n := by omega
      simp only [blockSelector, Nat.not_even_two_mul_add_one,
        if_false, hdiv, hn, if_true]
    have hAlternating := hAll blockSelector hblockSelector
    change AllAlternatingPrefixesRealized values low high
      (base ∘ blockSelector) at hAlternating
    let support : Finset ℕ := E ∪ F
    let bound : ℕ := support.sup id + 1
    obtain ⟨point, hpoint⟩ := hAlternating (2 * bound)
    refine ⟨point, ?_, ?_⟩
    · intro i hiE
      have hiNotF : i ∉ F :=
        Finset.disjoint_left.mp hdisjoint hiE
      have hiSupport : i ∈ support := Finset.mem_union_left F hiE
      have hiLe : i ≤ support.sup id :=
        Finset.le_sup (f := id) hiSupport
      let position : Fin (2 * bound) := ⟨2 * i, by
        dsimp only [bound]
        omega⟩
      have hp := hpoint position
      have hpositionEven : Even (position : ℕ) := by
        exact ⟨i, by simp only [position, two_mul]⟩
      simp only [hpositionEven, if_pos, Function.comp_apply] at hp
      simpa only [selected, position, hblockEven i hiNotF] using hp
    · intro i hiF
      have hiSupport : i ∈ support := Finset.mem_union_right E hiF
      have hiLe : i ≤ support.sup id :=
        Finset.le_sup (f := id) hiSupport
      let position : Fin (2 * bound) := ⟨2 * i + 1, by
        dsimp only [bound]
        omega⟩
      have hp := hpoint position
      have hpositionNotEven : ¬ Even (position : ℕ) := by
        change ¬ Even (2 * i + 1)
        exact Nat.not_even_two_mul_add_one i
      simp only [hpositionNotEven, if_false, Function.comp_apply] at hp
      simpa only [selected, position, hblockOdd i hiF] using hp
  · refine ⟨base, hbase, Or.inl ?_⟩
    intro point _
    by_contra hneither
    push Not at hneither
    have hlow : ∃ᶠ n in atTop,
        values (base n) point ≤ low := hneither.1
    have hhigh : ∃ᶠ n in atTop,
        high ≤ values (base n) point := hneither.2
    let predicate : ℕ → ℕ → Prop := fun position n ↦
      if Even position then values (base n) point ≤ low
      else high ≤ values (base n) point
    have hfrequent : ∀ position,
        ∃ᶠ n in atTop, predicate position n := by
      intro position
      by_cases hposition : Even position
      · simpa only [predicate, hposition, if_pos] using hlow
      · simpa only [predicate, hposition, if_false] using hhigh
    obtain ⟨subsequence, hsubsequence, hpattern⟩ :=
      exists_strictMono_satisfying_of_positionwise_frequently hfrequent
    apply hNone subsequence hsubsequence
    change AllAlternatingPrefixesRealized values low high
      (base ∘ subsequence)
    intro length
    exact ⟨point, fun i ↦ hpattern i⟩

/-- If the function sequence contains no independent subsequence, the
combinatorial level-pair dichotomy selects a subsequence whose low/high pairs
converge. -/
theorem exists_thresholdPairConvergentSubsequence_of_dichotomy
    {α : Type u} {values : ℕ → α → ℝ} {low high : ℝ}
    (hDichotomy : ThresholdPairSubsequenceDichotomy.{u})
    (hgap : low < high)
    (hNoIndependent : ¬ HasIndependentSubsequence values) :
    ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      ThresholdPairConverges
        (fun n point ↦ values (subsequence n) point) low high := by
  obtain ⟨subsequence, hsubsequence, hconverges | hindependent⟩ :=
    hDichotomy α values low high hgap
  · exact ⟨subsequence, hsubsequence, hconverges⟩
  · exfalso
    apply hNoIndependent
    exact ⟨subsequence, hsubsequence,
      low, high, hgap, hindependent⟩

/-- Failure to contain an independent subsequence is inherited by every
subsequence. -/
theorem not_hasIndependentSubsequence_comp
    {α : Type*} {values : ℕ → α → ℝ}
    (hNoIndependent : ¬ HasIndependentSubsequence values)
    (subsequence : ℕ → ℕ) (hsubsequence : StrictMono subsequence) :
    ¬ HasIndependentSubsequence
      (fun n point ↦ values (subsequence n) point) := by
  rintro ⟨further, hfurther, hindependent⟩
  apply hNoIndependent
  refine ⟨subsequence ∘ further, hsubsequence.comp hfurther, ?_⟩
  simpa [Function.comp_def] using hindependent

/-- Choose and bundle the threshold-pair-convergent subsequence supplied by
the fixed-pair dichotomy when independence is excluded. -/
noncomputable def convergentThresholdSubsequence
    {α : Type u} {values : ℕ → α → ℝ} {low high : ℝ}
    (hDichotomy : ThresholdPairSubsequenceDichotomy.{u})
    (hgap : low < high)
    (hNoIndependent : ¬ HasIndependentSubsequence values) :
    NatSubsequence :=
  ⟨Classical.choose
      (exists_thresholdPairConvergentSubsequence_of_dichotomy
        hDichotomy hgap hNoIndependent),
    (Classical.choose_spec
      (exists_thresholdPairConvergentSubsequence_of_dichotomy
        hDichotomy hgap hNoIndependent)).1⟩

/-- The bundled choice above has the promised threshold-pair convergence. -/
theorem convergentThresholdSubsequence_spec
    {α : Type u} {values : ℕ → α → ℝ} {low high : ℝ}
    (hDichotomy : ThresholdPairSubsequenceDichotomy.{u})
    (hgap : low < high)
    (hNoIndependent : ¬ HasIndependentSubsequence values) :
    ThresholdPairConverges
      (fun n point ↦
        values (convergentThresholdSubsequence
          hDichotomy hgap hNoIndependent n) point)
      low high :=
  (Classical.choose_spec
    (exists_thresholdPairConvergentSubsequence_of_dichotomy
      hDichotomy hgap hNoIndependent)).2

/-- Threshold-pair convergence of a tail implies convergence of the whole
sequence, since either eventual avoidance property is insensitive to a finite
prefix. -/
theorem ThresholdPairConvergesOn.of_add_left
    {α : Type*} {values : ℕ → α → ℝ} {subset : Set α}
    {low high : ℝ} (k : ℕ)
    (hconverges : ThresholdPairConvergesOn
      (fun n point ↦ values (k + n) point) low high subset) :
    ThresholdPairConvergesOn values low high subset := by
  intro point hpoint
  rcases hconverges point hpoint with hlow | hhigh
  · left
    rw [eventually_atTop] at hlow ⊢
    obtain ⟨N, hN⟩ := hlow
    refine ⟨k + N, ?_⟩
    intro n hn
    have hk : k ≤ n := by omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact hN m (by omega)
  · right
    rw [eventually_atTop] at hhigh ⊢
    obtain ⟨N, hN⟩ := hhigh
    refine ⟨k + N, ?_⟩
    intro n hn
    have hk : k ≤ n := by omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact hN m (by omega)

/-- Under the fixed-pair combinatorial dichotomy, a sequence containing no
independent subsequence has one subsequence on which every strict rational
threshold pair converges. The proof recursively refines along an enumeration
of rational pairs and then takes the nested diagonal. -/
theorem exists_subsequence_rational_thresholdPairsConverge_of_dichotomy
    {α : Type u} {values : ℕ → α → ℝ}
    (hDichotomy : ThresholdPairSubsequenceDichotomy.{u})
    (hNoIndependent : ¬ HasIndependentSubsequence values) :
    ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      ∀ q r : ℚ, q < r →
        ThresholdPairConverges
          (fun n point ↦ values (subsequence n) point)
          (q : ℝ) (r : ℝ) := by
  classical
  let pairs : ℕ → ℚ × ℚ :=
    Classical.choose (exists_surjective_nat (ℚ × ℚ))
  have hpairs : Function.Surjective pairs :=
    Classical.choose_spec (exists_surjective_nat (ℚ × ℚ))
  let refineAt : ℕ → NatSubsequence → NatSubsequence :=
    fun n current ↦
      if hgap : (pairs n).1 < (pairs n).2 then
        current.comp <|
          convergentThresholdSubsequence hDichotomy
            (show ((pairs n).1 : ℝ) < ((pairs n).2 : ℝ) by
              exact_mod_cast hgap)
            (not_hasIndependentSubsequence_comp hNoIndependent
              current current.strictMono_indices)
      else current
  let tower : ℕ → NatSubsequence :=
    fun n ↦ Nat.rec NatSubsequence.id
      (fun k current ↦ refineAt k current) n
  have htowerSucc (n : ℕ) : tower (n + 1) = refineAt n (tower n) := by
    simp only [tower]
  have hnested (n : ℕ) :
      Set.range (tower (n + 1) : ℕ → ℕ) ⊆
        Set.range (tower n : ℕ → ℕ) := by
    rw [htowerSucc]
    simp only [refineAt]
    split_ifs
    · change Set.range
          ((tower n).indices ∘
            (convergentThresholdSubsequence _ _ _).indices) ⊆
          Set.range (tower n).indices
      exact Set.range_comp_subset_range _ _
    · exact Set.Subset.rfl
  have htowerConverges (n : ℕ)
      (hgap : (pairs n).1 < (pairs n).2) :
      ThresholdPairConverges
        (fun m point ↦ values (tower (n + 1) m) point)
        ((pairs n).1 : ℝ) ((pairs n).2 : ℝ) := by
    rw [htowerSucc]
    simp only [refineAt, dif_pos hgap, NatSubsequence.comp_apply]
    exact convergentThresholdSubsequence_spec hDichotomy
      (by exact_mod_cast hgap)
      (not_hasIndependentSubsequence_comp hNoIndependent
        (tower n) (tower n).strictMono_indices)
  obtain ⟨diagonal, hdiagonal, htailFactors⟩ :=
    exists_strictMono_diagonal_of_nested
      (fun n ↦ tower n) (fun n ↦ (tower n).strictMono_indices) hnested
  refine ⟨diagonal, hdiagonal, ?_⟩
  intro q r hqr
  obtain ⟨n, hn⟩ := hpairs (q, r)
  have hgap : (pairs n).1 < (pairs n).2 := by
    simpa only [hn] using hqr
  obtain ⟨factor, hfactor, htail⟩ := htailFactors (n + 1)
  have htailConverges : ThresholdPairConverges
      (fun m point ↦ values (diagonal (n + 1 + m)) point)
      (q : ℝ) (r : ℝ) := by
    have hselected :=
      (htowerConverges n hgap).comp_strictMono factor hfactor
    have hvalueTail :
        (fun m point ↦ values (diagonal (n + 1 + m)) point) =
          (fun m point ↦ values (tower (n + 1) (factor m)) point) := by
      funext m point
      rw [congrFun htail m]
      rfl
    rw [hvalueTail]
    simpa only [hn] using hselected
  exact htailConverges.of_add_left (n + 1)

/-- The fixed-threshold pair dichotomy implies the full pointwise BFT
dichotomy. For a sequence without an independent subsequence, diagonalize all
rational gaps and reconstruct scalar pointwise convergence from them. -/
theorem bftPointwiseDichotomy_of_thresholdPairSubsequenceDichotomy
    (hDichotomy : ThresholdPairSubsequenceDichotomy.{u})
    (α : Type u) [TopologicalSpace α] :
    BFTPointwiseDichotomy α := by
  intro values _hcontinuous hbounded
  by_cases hIndependent : HasIndependentSubsequence values
  · exact Or.inr hIndependent
  · left
    obtain ⟨subsequence, hsubsequence, hconverges⟩ :=
      exists_subsequence_rational_thresholdPairsConverge_of_dichotomy
        hDichotomy hIndependent
    refine ⟨subsequence, hsubsequence, ?_⟩
    exact pointwiseConvergence_of_rational_thresholdPairConvergence
      (fun n point ↦ hbounded (subsequence n) point) hconverges


/-- The closed-set Galvin--Prikry theorem, now discharged from Galvin's proved
open-prefix lemma. -/
theorem galvinPrikryClosedSubsequenceRamsey :
    GalvinPrikryClosedSubsequenceRamsey :=
  galvinPrikryClosedSubsequenceRamsey_of_openPrefixRamsey
    galvinOpenPrefixRamsey

/-- Rosenthal's fixed-threshold pair dichotomy, with no remaining abstract
Ramsey premise. -/
theorem thresholdPairSubsequenceDichotomy :
    ThresholdPairSubsequenceDichotomy.{u} :=
  thresholdPairSubsequenceDichotomy_of_galvinPrikry
    galvinPrikryClosedSubsequenceRamsey

/-- The full pointwise BFT dichotomy on an arbitrary topological space,
specialized from the unconditional threshold-pair theorem. -/
theorem bftPointwiseDichotomy
    (α : Type u) [TopologicalSpace α] :
    BFTPointwiseDichotomy α :=
  bftPointwiseDichotomy_of_thresholdPairSubsequenceDichotomy
    thresholdPairSubsequenceDichotomy α


/-- Every row sequence has a subsequence whose evaluation functions converge
pointwise on the concrete local parameter type space. -/
def HasPointwiseConvergentSubsequenceOnLocalType {Symbol : Type w}
    (M : MultiStructure.{u, v, w} Symbol)
    (φ : MultiFormula Symbol 1 1) : Prop :=
  ∀ rows : ℕ → M.Row,
    HasPointwiseConvergentSubsequence
      (localTypeEvaluationSequence (φ := φ) rows)

/-- The local evaluation sequence consists of continuous functions. -/
theorem continuous_localTypeEvaluationSequence
    {Symbol : Type w} {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1} (rows : ℕ → M.Row) :
    ∀ n, Continuous (localTypeEvaluationSequence (φ := φ) rows n) := by
  intro n
  exact continuous_localTypeValue (rows n)

/-- Every local evaluation lies in the bounded truth-value interval. -/
theorem localTypeEvaluationSequence_mem_Icc
    {Symbol : Type w} {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1} (rows : ℕ → M.Row) :
    ∀ n type,
      localTypeEvaluationSequence (φ := φ) rows n type ∈
        Set.Icc (0 : ℝ) 1 := by
  intro n type
  exact (type.1 (rows n)).2

/-- NIP excludes not only an independent evaluation sequence, but an
independent subsequence of every row-indexed evaluation sequence. The latter
is itself the evaluation sequence of the corresponding subsequence of rows. -/
theorem IsNIPOnStructure.no_independentSubsequence_localTypeEvaluationSequence
    {Symbol : Type w} {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1}
    (hNIP : IsNIPOnStructure M φ) (rows : ℕ → M.Row) :
    ¬ HasIndependentSubsequence
      (localTypeEvaluationSequence (φ := φ) rows) := by
  intro hindependentSubsequence
  obtain ⟨subsequence, _hsubsequence, hindependent⟩ :=
    hindependentSubsequence
  have hNoIndependent :=
    isNIPOnStructure_iff_no_independent_localTypeEvaluationSequence.mp hNIP
  apply hNoIndependent (rows ∘ subsequence)
  simpa [localTypeEvaluationSequence, Function.comp_def] using hindependent

/-- A fixed-gap IP witness supplies, along every row subsequence, a local type
whose values alternate across the original gap. In particular, that
subsequence cannot converge pointwise on the local type space. -/
theorem HasInfiniteIPWitness.no_pointwiseConvergentSubsequence_localType
    {Symbol : Type w} {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1} {low high : ℝ}
    (hgap : low < high) (hIP : HasInfiniteIPWitness M φ low high)
    (subsequence : ℕ → ℕ) (hsubsequence : StrictMono subsequence) :
    ¬ ∀ type : LocalParameterType M φ, ∃ limit : ℝ,
        Tendsto
          (fun n ↦ localTypeValue (Classical.choose hIP (subsequence n)) type)
          atTop (𝓝 limit) := by
  classical
  let rows : ℕ → M.Row := Classical.choose hIP
  have hrows := Classical.choose_spec hIP
  have hindependent : HasIndependentSequence
      (localTypeEvaluationSequence (φ := φ) rows) := by
    refine ⟨low, high, hgap, ?_⟩
    intro E F hdisjoint
    obtain ⟨parameter, hlow, hhigh⟩ := hrows E F hdisjoint
    refine ⟨homeParameterType M φ parameter, ?_, ?_⟩
    · intro i hi
      change φ.binaryValue M (rows i) parameter ≤ low
      exact hlow i hi
    · intro i hi
      change high ≤ φ.binaryValue M (rows i) parameter
      exact hhigh i hi
  simpa [rows, localTypeEvaluationSequence] using
    hindependent.no_pointwiseConvergence_along
      (continuous_localTypeEvaluationSequence rows)
      subsequence hsubsequence

/-- The pointwise-subsequence property on the concrete local type space
implies NIP on the distinguished structure. This is the elementary direction
of the model-theoretic BFT equivalence. -/
theorem isNIPOnStructure_of_pointwiseConvergentSubsequenceOnLocalType
    {Symbol : Type w} {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1}
    (hpointwise : HasPointwiseConvergentSubsequenceOnLocalType M φ) :
    IsNIPOnStructure M φ := by
  rintro ⟨low, high, hgap, hIP⟩
  obtain ⟨subsequence, hsubsequence, hconverges⟩ :=
    hpointwise (Classical.choose hIP)
  exact hIP.no_pointwiseConvergentSubsequence_localType
    hgap subsequence hsubsequence hconverges

/-- The abstract BFT dichotomy supplies the NIP-to-subsequence
direction on the concrete local type space. All formula-specific hypotheses
are discharged by continuity and `[0,1]`-boundedness of coordinate
evaluation. -/
theorem hasPointwiseConvergentSubsequenceOnLocalType_of_bftPointwiseDichotomy
    {Symbol : Type w} {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1}
    (hBFT : BFTPointwiseDichotomy (LocalParameterType M φ))
    (hNIP : IsNIPOnStructure M φ) :
    HasPointwiseConvergentSubsequenceOnLocalType M φ := by
  intro rows
  rcases hBFT (localTypeEvaluationSequence (φ := φ) rows)
      (continuous_localTypeEvaluationSequence rows)
      (localTypeEvaluationSequence_mem_Icc rows) with
    hconverges | hindependent
  · exact hconverges
  · exact
      (hNIP.no_independentSubsequence_localTypeEvaluationSequence
        rows hindependent).elim

/-- Subject only to the abstract BFT dichotomy, the concrete local type space
gives the full model-theoretic pointwise-subsequence characterization. -/
theorem isNIPOnStructure_iff_pointwiseConvergentSubsequenceOnLocalType_of_bft
    {Symbol : Type w} {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1}
    (hBFT : BFTPointwiseDichotomy (LocalParameterType M φ)) :
    IsNIPOnStructure M φ ↔
      HasPointwiseConvergentSubsequenceOnLocalType M φ :=
  ⟨hasPointwiseConvergentSubsequenceOnLocalType_of_bftPointwiseDichotomy
      hBFT,
    isNIPOnStructure_of_pointwiseConvergentSubsequenceOnLocalType⟩

/-- The local-type sequential criterion with no additional modulus or
separability hypothesis. The general pointwise dichotomy supplies the BFT
input, and local types are the compact closure of home profiles. -/
theorem isNIPOnStructure_iff_pointwiseConvergentSubsequenceOnLocalType_general
    {Symbol : Type w} {M : MultiStructure.{u, v, w} Symbol}
    {φ : MultiFormula Symbol 1 1} :
    IsNIPOnStructure M φ ↔
      HasPointwiseConvergentSubsequenceOnLocalType M φ :=
  isNIPOnStructure_iff_pointwiseConvergentSubsequenceOnLocalType_of_bft
    (bftPointwiseDichotomy _)


end MultiFormula

end

end NormFormula.ContinuousLogic
