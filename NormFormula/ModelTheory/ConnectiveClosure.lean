import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.SymmDiff
import NormFormula.Combinatorics.MetricPacking
import NormFormula.Combinatorics.StrongPairGrowth
import NormFormula.ModelTheory.LocalNIP

/-!
# The finite-pattern connective interface

Mathlib does not currently provide the continuous-logic theorem that NIP is
closed under continuous connectives.  This module isolates the exact semantic
principle required here, without adding it as an axiom.  It also verifies the
analytic part for the particular Euclidean connective used to reconstruct the
`Y`-norm.
-/

namespace NormFormula

/-- A binary real-valued function is bounded on each pair of norm balls. -/
def IsBoundedOnNormBalls {X Y : Type*} [Norm X] [Norm Y]
    (value : X → Y → ℝ) : Prop :=
  ∀ R_x R_y : ℝ, ∃ C : ℝ, ∀ x y,
    ‖x‖ ≤ R_x → ‖y‖ ≤ R_y → |value x y| ≤ C

/-- A binary connective preserves bounded local NIP for bounded-on-balls
input predicates.  This is the precise finite-pattern closure obligation
corresponding to the manuscript's continuous-connectives lemma. -/
def PreservesBoundedLocalNIP₂ (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ {X Y : Type} [Norm X] [Norm Y] (f g : X → Y → ℝ),
    IsBoundedOnNormBalls f → IsBoundedOnNormBalls g →
    IsBoundedLocalNIP f → IsBoundedLocalNIP g →
    IsBoundedLocalNIP fun x y ↦ F (f x y) (g x y)

/-- The Euclidean connective used in the definition of every augmented norm. -/
noncomputable def euclideanConnective (a b : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 + b ^ 2)

/-- The Euclidean connective is the ordinary norm of the associated complex
number. -/
theorem euclideanConnective_eq_complex_norm (a b : ℝ) :
    euclideanConnective a b = ‖(⟨a, b⟩ : ℂ)‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  rfl

/-- Sharp Euclidean reverse-triangle estimate for the connective. -/
theorem abs_euclideanConnective_sub_le (a b c d : ℝ) :
    |euclideanConnective a b - euclideanConnective c d| ≤
      Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
  rw [euclideanConnective_eq_complex_norm,
    euclideanConnective_eq_complex_norm]
  calc
    |‖(⟨a, b⟩ : ℂ)‖ - ‖(⟨c, d⟩ : ℂ)‖| ≤
        ‖(⟨a, b⟩ : ℂ) - (⟨c, d⟩ : ℂ)‖ :=
      abs_norm_sub_norm_le _ _
    _ = Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
      rw [Complex.norm_eq_sqrt_sq_add_sq]
      rfl

/-- With the standard max metric on `ℝ × ℝ`, the Euclidean connective is
`√2`-Lipschitz. -/
theorem euclideanConnective_dist_le (p q : ℝ × ℝ) :
    dist (euclideanConnective p.1 p.2) (euclideanConnective q.1 q.2) ≤
      Real.sqrt 2 * dist p q := by
  let D := dist p q
  have hfirst : |p.1 - q.1| ≤ D := by
    dsimp [D]
    rw [Prod.dist_eq]
    simp [Real.dist_eq]
  have hsecond : |p.2 - q.2| ≤ D := by
    dsimp [D]
    rw [Prod.dist_eq]
    simp [Real.dist_eq]
  have hsquares : (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 ≤ 2 * D ^ 2 := by
    nlinarith [sq_le_sq₀ (abs_nonneg _) (dist_nonneg : 0 ≤ D) |>.2 hfirst,
      sq_le_sq₀ (abs_nonneg _) (dist_nonneg : 0 ≤ D) |>.2 hsecond,
      sq_abs (p.1 - q.1), sq_abs (p.2 - q.2)]
  have hroot := Real.sqrt_le_sqrt hsquares
  have hD : 0 ≤ D := dist_nonneg
  have hrhs : Real.sqrt (2 * D ^ 2) = Real.sqrt 2 * D := by
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ)), Real.sqrt_sq hD]
  rw [Real.dist_eq]
  exact (abs_euclideanConnective_sub_le p.1 p.2 q.1 q.2).trans
    (hroot.trans_eq hrhs)

/-- Consequently the Euclidean connective is uniformly continuous on its
whole domain. -/
theorem euclideanConnective_uniformContinuous :
    UniformContinuous fun p : ℝ × ℝ ↦ euclideanConnective p.1 p.2 := by
  let K : NNReal := ⟨Real.sqrt 2, Real.sqrt_nonneg _⟩
  apply (LipschitzWith.of_dist_le_mul (K := K) ?_).uniformContinuous
  intro p q
  simpa [K] using euclideanConnective_dist_le p q

/-- A fixed gap between two Euclidean-connective values forces a definite
gap in at least one input coordinate.  This is the metric separation step in
the finite-pattern proof of connective closure. -/
theorem euclideanConnective_gap_forces_coordinate_gap
    {a b c d low high : ℝ}
    (hgap : low ≤ high)
    (hlow : euclideanConnective a b ≤ low)
    (hhigh : high ≤ euclideanConnective c d) :
    (high - low) / Real.sqrt 2 ≤ max |c - a| |d - b| := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have houtput : high - low ≤
      euclideanConnective c d - euclideanConnective a b := by
    linarith
  have hnonneg : 0 ≤
      euclideanConnective c d - euclideanConnective a b := by
    exact sub_nonneg.mpr (hlow.trans (hgap.trans hhigh))
  have hlipschitz := euclideanConnective_dist_le (c, d) (a, b)
  have hlipschitz' :
      euclideanConnective c d - euclideanConnective a b ≤
        Real.sqrt 2 * max |c - a| |d - b| := by
    simpa [Real.dist_eq, Prod.dist_eq, abs_of_nonneg hnonneg] using hlipschitz
  exact (div_le_iff₀ hsqrt).2 (by
    simpa [mul_comm] using houtput.trans hlipschitz')

/-- An `n`-dimensional IP pattern for the Euclidean combination supplies
`2^n` parameter evaluations which are pairwise separated, in the rowwise
maximum metric, in at least one of the two input coordinates.  The remaining
connective-closure problem is therefore a scale-sensitive packing bound for
the two input classes. -/
theorem IsIPPattern.exists_pairEvaluations_coordinateSeparated
    {n : ℕ} {Parameter : Type*}
    {f g : Fin n → Parameter → ℝ} {low high : ℝ}
    (hip : IsIPPattern
      (fun i parameter ↦ euclideanConnective (f i parameter) (g i parameter))
      low high)
    (hgap : low < high) :
    ∃ parameters : Finset (Fin n) → Parameter,
      ∀ S T, S ≠ T → ∃ i,
        (high - low) / Real.sqrt 2 ≤
          max |f i (parameters S) - f i (parameters T)|
            |g i (parameters S) - g i (parameters T)| := by
  classical
  choose parameters hparameters using hip
  refine ⟨parameters, ?_⟩
  intro S T hST
  obtain ⟨i, hi⟩ := (Finset.symmDiff_nonempty.mpr hST)
  rw [Finset.mem_symmDiff] at hi
  rcases hi with ⟨hiS, hiT⟩ | ⟨hiT, hiS⟩
  · refine ⟨i, ?_⟩
    exact euclideanConnective_gap_forces_coordinate_gap
      hgap.le ((hparameters T).2 i hiT) ((hparameters S).1 i hiS)
  · refine ⟨i, ?_⟩
    have hseparation := euclideanConnective_gap_forces_coordinate_gap
      hgap.le ((hparameters S).2 i hiS) ((hparameters T).1 i hiT)
    simpa [abs_sub_comm] using hseparation

/-- Uniform finiteness of fat-shattered families on each pair of norm balls
and at each positive scale. -/
def HasFiniteFatShatteringOnNormBalls
    {X Y : Type*} [Norm X] [Norm Y] (value : X → Y → ℝ) : Prop :=
  ∀ R_x R_y ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ (n : ℕ) (rows : Fin n → X),
      (∀ i, ‖rows i‖ ≤ R_x) →
      IsFatShattered (boundedBinaryValue value rows R_y) ε → n < N

/-- Boundedness and fixed-common-gap local NIP imply finite fat-shattering
dimension at every positive scale.  Compactness of a bounded real interval
gives finitely many short bands for the row-dependent thresholds; pigeonhole
and `exists_ipPattern_restriction_of_fat_witness_finite_banding` then turn a
large fat-shattered family into a forbidden common-gap pattern. -/
theorem hasFiniteFatShatteringOnNormBalls_of_boundedLocalNIP
    {X Y : Type*} [Norm X] [Norm Y] {value : X → Y → ℝ}
    (hbounded : IsBoundedOnNormBalls value)
    (hlocal : IsBoundedLocalNIP value) :
    HasFiniteFatShatteringOnNormBalls value := by
  classical
  intro R_x R_y ε hε
  obtain ⟨C, hC⟩ := hbounded R_x R_y
  obtain ⟨centersSet, hcentersSubset, hcentersFinite, hcover⟩ :=
    finite_cover_balls_of_compact
      (s := Set.Icc (-|C|) |C|) isCompact_Icc
      (show 0 < ε / 2 by linarith)
  let centers : Finset ℝ := insert 0 hcentersFinite.toFinset
  let Center := ↑centers
  have hzeroCenter : (0 : ℝ) ∈ centers := by
    exact Finset.mem_insert_self 0 hcentersFinite.toFinset
  letI : Nonempty Center :=
    ⟨⟨0, hzeroCenter⟩⟩
  let base : Center → ℝ := fun center ↦ center.1 - ε / 2
  have hcenterGap : ∀ center : Center,
      base center < base center + ε := by
    intro center
    linarith
  choose dimension hdimension using fun center : Center ↦
    hlocal R_x R_y (base center) (base center + ε)
      (hcenterGap center)
  let maxDimension : ℕ := Finset.univ.sup dimension
  refine ⟨Fintype.card Center * maxDimension, ?_⟩
  intro n rows hrows hfat
  by_contra hn
  have hcard : Fintype.card Center * maxDimension ≤ n :=
    Nat.le_of_not_gt hn
  obtain ⟨threshold, hthreshold⟩ := hfat
  have hthresholdBound : ∀ r, threshold r ∈ Set.Icc (-|C|) |C| := by
    intro r
    obtain ⟨highParameter, hhigh, _⟩ :=
      hthreshold (Finset.univ : Finset (Fin n))
    obtain ⟨lowParameter, _, hlow⟩ :=
      hthreshold (∅ : Finset (Fin n))
    have hhighBound :
        |value (rows r) highParameter.1| ≤ |C| :=
      (hC (rows r) highParameter.1 (hrows r) highParameter.2).trans
        (le_abs_self C)
    have hlowBound :
        |value (rows r) lowParameter.1| ≤ |C| :=
      (hC (rows r) lowParameter.1 (hrows r) lowParameter.2).trans
        (le_abs_self C)
    have hthresholdUpper : threshold r ≤ |C| := by
      have hr := hhigh r (Finset.mem_univ r)
      have hv := (abs_le.mp hhighBound).2
      change threshold r + ε ≤ value (rows r) highParameter.1 at hr
      linarith
    have hthresholdLower : -|C| ≤ threshold r := by
      have hr := hlow r (by simp)
      have hv := (abs_le.mp hlowBound).1
      change value (rows r) lowParameter.1 ≤ threshold r - ε at hr
      linarith
    exact ⟨hthresholdLower, hthresholdUpper⟩
  have hcenter : ∀ r, ∃ center : ℝ, center ∈ centersSet ∧
      dist (threshold r) center < ε / 2 := by
    intro r
    have hr := hcover (hthresholdBound r)
    simp only [Set.mem_iUnion, Metric.mem_ball] at hr
    obtain ⟨center, hcenterMem, hdist⟩ := hr
    exact ⟨center, hcenterMem, hdist⟩
  choose center hcenterMem hcenterDist using hcenter
  let color : Fin n → Center := fun r ↦
    ⟨center r, by
      apply Finset.mem_insert_of_mem
      exact hcentersFinite.mem_toFinset.mpr (hcenterMem r)⟩
  have hband : ∀ r, base (color r) ≤ threshold r ∧
      threshold r ≤ base (color r) + ε := by
    intro r
    have hdist := hcenterDist r
    rw [Real.dist_eq] at hdist
    have habs := abs_lt.mp hdist
    dsimp [base, color]
    constructor <;> linarith
  obtain ⟨chosenCenter, embedding, hip⟩ :=
    exists_ipPattern_restriction_of_fat_witness_finite_banding
      hthreshold color base hband (by simpa using hcard)
  have hchosenLe : dimension chosenCenter ≤ maxDimension := by
    exact Finset.le_sup (f := dimension) (Finset.mem_univ chosenCenter)
  have hforbidden : maxDimension < dimension chosenCenter := by
    apply hdimension chosenCenter maxDimension
      (fun i ↦ rows (embedding i))
    · intro i
      exact hrows (embedding i)
    · simpa [NormFormula.boundedBinaryValue] using hip
  exact (Nat.not_lt_of_ge hchosenLe) hforbidden

/-- A global finite fat-shattering bound on fixed norm balls restricts
uniformly to every finite subfamily of sampled evaluations and every selected
finite row subset. -/
theorem exists_finiteEvaluationFamily_fatDimensionBound
    {X Y : Type*} [Norm X] [Norm Y] {value : X → Y → ℝ}
    (hfinite : HasFiniteFatShatteringOnNormBalls value)
    (R_x R_y margin : ℝ) (hmargin : 0 < margin) :
    ∃ dimension : ℕ, ∀ (n : ℕ) (rows : Fin n → X),
      (∀ i, ‖rows i‖ ≤ R_x) →
      ∀ (parameters : Finset (Fin n) → ClosedNormBall Y R_y)
        (family : Finset (Fin n → ℝ)),
        family ⊆ Finset.univ.image
          (fun subset row ↦ value (rows row) (parameters subset).1) →
        HasFatShatteringDimensionAtMostOn
          family Finset.univ margin dimension := by
  classical
  obtain ⟨dimension, hdimension⟩ := hfinite R_x R_y margin hmargin
  refine ⟨dimension, ?_⟩
  intro n rows hrows parameters family hfamily selectedRows _ hselectedFat
  have hpreimage : ∀ evaluation : ↥family,
      ∃ parameter : ClosedNormBall Y R_y, ∀ row,
        value (rows row) parameter.1 = evaluation.1 row := by
    intro evaluation
    have hevaluation := hfamily evaluation.2
    obtain ⟨subset, _, heq⟩ := Finset.mem_image.mp hevaluation
    refine ⟨parameters subset, ?_⟩
    intro row
    exact congrFun heq row
  choose preimage hpreimageValue using hpreimage
  have hfatParameters : IsFatShattered
      (fun row : ↥selectedRows ↦
        fun parameter : ClosedNormBall Y R_y ↦
          value (rows row.1) parameter.1) margin := by
    apply hselectedFat.reparam preimage
    intro row evaluation
    exact hpreimageValue evaluation row.1
  let rowEquiv : Fin (Fintype.card ↥selectedRows) ≃ ↥selectedRows :=
    (Fintype.equivFin ↥selectedRows).symm
  have hfatFin := hfatParameters.comp_embedding rowEquiv.toEmbedding
  have hcard : Fintype.card ↥selectedRows < dimension := by
    apply hdimension (Fintype.card ↥selectedRows)
      (fun i ↦ rows (rowEquiv i).1)
    · intro i
      exact hrows (rowEquiv i).1
    · simpa [boundedBinaryValue, rowEquiv] using hfatFin
  simpa [Fintype.card_coe] using hcard.le

/-- Polynomial-size strict sup-norm covers for every powerset-indexed finite
parameter sample on fixed norm balls.  This is the precise metric-entropy
property needed after extracting the `2^n` evaluations of an IP pattern. -/
def HasPolynomialPowersetEvaluationCoversOnNormBalls
    {X Y : Type*} [Norm X] [Norm Y] (value : X → Y → ℝ) : Prop :=
  ∀ R_x R_y radius : ℝ, 0 < radius →
    ∃ C d : ℕ, ∀ (n : ℕ) (rows : Fin n → X),
      (∀ i, ‖rows i‖ ≤ R_x) →
      ∀ parameters : Finset (Fin n) → ClosedNormBall Y R_y,
        ∃ centers : Finset (Fin n → ℝ),
          IsEvaluationSupCover
            (fun row subset ↦ value (rows row) (parameters subset).1)
            Finset.univ centers radius ∧
          centers.card ≤ C * (n + 1) ^ d

/-- Polynomial evaluation covers for two inputs rule out arbitrarily large
fixed-gap IP patterns for their Euclidean combination.  The proof combines
the coordinate-separation reduction, the product-cover counting lemma, and
exponential domination of every fixed polynomial. -/
theorem euclideanConnective_isBoundedLocalNIP_of_polynomialEvaluationCovers
    {X Y : Type*} [Norm X] [Norm Y] {f g : X → Y → ℝ}
    (hfCovers : HasPolynomialPowersetEvaluationCoversOnNormBalls f)
    (hgCovers : HasPolynomialPowersetEvaluationCoversOnNormBalls g) :
    IsBoundedLocalNIP fun x y ↦ euclideanConnective (f x y) (g x y) := by
  intro R_x R_y low high hgap
  let separation : ℝ := (high - low) / Real.sqrt 2
  let radius : ℝ := separation / 3
  have hseparation : 0 < separation := by
    dsimp [separation]
    exact div_pos (sub_pos.mpr hgap) (Real.sqrt_pos.2 (by norm_num))
  have hradius : 0 < radius := by
    dsimp [radius]
    positivity
  obtain ⟨Cf, df, hfCovers⟩ := hfCovers R_x R_y radius hradius
  obtain ⟨Cg, dg, hgCovers⟩ := hgCovers R_x R_y radius hradius
  obtain ⟨N, hN⟩ := exists_polynomial_lt_two_pow_bound
    (Cf * Cg) (df + dg)
  refine ⟨N, ?_⟩
  intro n rows hrows hip
  by_contra hn
  have hNle : N ≤ n := Nat.le_of_not_gt hn
  have hip' : IsIPPattern
      (fun (i : Fin n) (parameter : ClosedNormBall Y R_y) ↦
        euclideanConnective
          (f (rows i) parameter.1) (g (rows i) parameter.1))
      low high := by
    simpa [boundedBinaryValue] using hip
  obtain ⟨parameters, hparameters⟩ :=
    hip'.exists_pairEvaluations_coordinateSeparated hgap
  obtain ⟨fCenters, hfCover, hfCard⟩ :=
    hfCovers n rows hrows parameters
  obtain ⟨gCenters, hgCover, hgCard⟩ :=
    hgCovers n rows hrows parameters
  have htwo : 2 ^ n ≤ fCenters.card * gCenters.card := by
    apply two_pow_le_mul_card_of_powerset_coordinateSeparated_of_supCovers
      (f := fun row parameter ↦ f (rows row) parameter.1)
      (g := fun row parameter ↦ g (rows row) parameter.1)
      (radius := radius) parameters hfCover hgCover
    intro S T hST
    obtain ⟨row, hrow⟩ := hparameters S T hST
    refine ⟨row, ?_⟩
    calc
      radius + radius ≤ separation := by
        dsimp [radius]
        linarith
      _ ≤ max
          |f (rows row) (parameters S).1 -
            f (rows row) (parameters T).1|
          |g (rows row) (parameters S).1 -
            g (rows row) (parameters T).1| := hrow
  have hcoverCard : fCenters.card * gCenters.card ≤
      (Cf * Cg) * (n + 1) ^ (df + dg) := by
    calc
      fCenters.card * gCenters.card ≤
          (Cf * (n + 1) ^ df) * (Cg * (n + 1) ^ dg) :=
        Nat.mul_le_mul hfCard hgCard
      _ = (Cf * Cg) * (n + 1) ^ (df + dg) := by
        rw [pow_add]
        ring
  exact (Nat.not_lt_of_ge (htwo.trans hcoverCard)) (hN n hNle)

/-- Finite-sample sup-norm covers whose squared cardinality is eventually
smaller than `2^n`.  This is the correct entropy scale supplied by the
fat-shattering packing theorem: its standard bound is quasi-polynomial (and
hence subexponential), not necessarily a fixed-degree polynomial. -/
def HasSubexponentialPowersetEvaluationCoversOnNormBalls
    {X Y : Type*} [Norm X] [Norm Y] (value : X → Y → ℝ) : Prop :=
  ∀ R_x R_y radius : ℝ, 0 < radius →
    ∃ bound : ℕ → ℕ,
      (∀ᶠ n : ℕ in Filter.atTop, (bound n) ^ 2 < 2 ^ n) ∧
      ∀ (n : ℕ) (rows : Fin n → X),
        (∀ i, ‖rows i‖ ≤ R_x) →
        ∀ parameters : Finset (Fin n) → ClosedNormBall Y R_y,
          ∃ centers : Finset (Fin n → ℝ),
            IsEvaluationSupCover
              (fun row subset ↦ value (rows row) (parameters subset).1)
              Finset.univ centers radius ∧
            centers.card ≤ bound n

/-- Bounded local NIP supplies square-subexponential finite-sample evaluation
covers. This is the scale-sensitive Sauer packing theorem in the exact form
needed for connective closure. -/
theorem hasSubexponentialEvaluationCovers_of_boundedLocalNIP
    {X Y : Type*} [Norm X] [Norm Y] {value : X → Y → ℝ}
    (hbounded : IsBoundedOnNormBalls value)
    (hlocal : IsBoundedLocalNIP value) :
    HasSubexponentialPowersetEvaluationCoversOnNormBalls value := by
  classical
  intro R_x R_y radius hradius
  let mesh := radius / 2
  have hmesh : 0 < mesh := by
    dsimp [mesh]
    positivity
  obtain ⟨C, hC⟩ := hbounded R_x R_y
  let levelCount :=
    floorDiscretization mesh (2 * |C|) + 1
  have hfinite :=
    hasFiniteFatShatteringOnNormBalls_of_boundedLocalNIP
      hbounded hlocal
  obtain ⟨dimension, hdimension⟩ :=
    exists_finiteEvaluationFamily_fatDimensionBound
      hfinite R_x R_y (mesh / 2) (by positivity)
  let recurrentBound : ℕ → ℕ := fun n ↦
    strongPairIterationFamilySize n levelCount (Nat.sqrt n)
  let bound : ℕ → ℕ := fun n ↦
    if strongShatteringPairBound n levelCount dimension <
        2 ^ Nat.sqrt n then recurrentBound n else 2 ^ n
  refine ⟨bound, ?_, ?_⟩
  · filter_upwards
      [eventually_strongShatteringPairBound_lt_two_pow_sqrt
        levelCount dimension,
       eventually_sq_strongPairIterationFamilySize_sqrt_lt_two_pow
        levelCount] with n hpairCount hrecurrent
    simp [bound, recurrentBound, hpairCount, hrecurrent]
  · intro n rows hrows parameters
    by_cases hpairCount : strongShatteringPairBound n levelCount dimension <
        2 ^ Nat.sqrt n
    · obtain ⟨centers, hcover, hcentersCard⟩ :=
        exists_evaluationSupCover_of_separated_subfamily_card_lt
          (value := fun row subset ↦
            value (rows row) (parameters subset).1)
          (parameters := (Finset.univ : Finset (Finset (Fin n))))
          hradius (by
            intro family hfamily hseparated
            have hsteps : Nat.sqrt n ≤
                (Finset.univ : Finset (Fin n)).card := by
              simp
              exact Nat.sqrt_le_self n
            have hcount : strongShatteringPairBound
                (Fintype.card (Fin n))
                (floorDiscretization mesh (|C| - -|C|) + 1)
                dimension < 2 ^ Nat.sqrt n := by
              have hrange : |C| - -|C| = 2 * |C| := by ring
              simpa [levelCount, hrange] using hpairCount
            have hlower : ∀ f ∈ family,
                ∀ row ∈ (Finset.univ : Finset (Fin n)), -|C| ≤ f row := by
              intro f hf row _
              have hfEvaluation := hfamily hf
              obtain ⟨subset, _, rfl⟩ :=
                Finset.mem_image.mp hfEvaluation
              have hvalueBound := (hC (rows row) (parameters subset).1
                (hrows row) (parameters subset).2).trans (le_abs_self C)
              exact (abs_le.mp hvalueBound).1
            have hupper : ∀ f ∈ family,
                ∀ row ∈ (Finset.univ : Finset (Fin n)), f row ≤ |C| := by
              intro f hf row _
              have hfEvaluation := hfamily hf
              obtain ⟨subset, _, rfl⟩ :=
                Finset.mem_image.mp hfEvaluation
              have hvalueBound := (hC (rows row) (parameters subset).1
                (hrows row) (parameters subset).2).trans (le_abs_self C)
              exact (abs_le.mp hvalueBound).2
            have hpacking :=
              card_lt_strongPairIterationFamilySize_of_real_separated_of_bounds
                (family := family)
                (activeRows := (Finset.univ : Finset (Fin n)))
                (mesh := mesh) (lowerBound := -|C|) (upperBound := |C|)
                (dimension := dimension) (steps := Nat.sqrt n)
                hmesh hsteps hcount hlower hupper
                (by
                  intro f hf g hg hfg
                  obtain ⟨row, hrow⟩ :=
                    hseparated f hf g hg hfg
                  refine ⟨row, Finset.mem_univ row, ?_⟩
                  have htwomesh : 2 * mesh = radius := by
                    dsimp [mesh]
                    ring
                  rw [htwomesh]
                  exact hrow)
                (hdimension n rows hrows parameters family hfamily)
            have hrange : |C| + |C| = 2 * |C| := by ring
            change family.card < recurrentBound n
            simpa [recurrentBound, levelCount, hrange] using hpacking)
      refine ⟨centers, hcover, ?_⟩
      exact hcentersCard.le.trans_eq (by simp [bound, recurrentBound, hpairCount])
    · let evaluations : Finset (Fin n → ℝ) :=
          Finset.univ.image (fun subset row ↦
            value (rows row) (parameters subset).1)
      refine ⟨evaluations, ?_, ?_⟩
      · intro subset _
        refine ⟨(fun row ↦ value (rows row) (parameters subset).1), ?_, ?_⟩
        · exact Finset.mem_image.mpr
            ⟨subset, Finset.mem_univ subset, rfl⟩
        · intro row
          simpa using hradius
      · calc
          evaluations.card ≤ (Finset.univ : Finset (Finset (Fin n))).card :=
            Finset.card_image_le
          _ = 2 ^ n := by simp [Fintype.card_finset]
          _ = bound n := by simp [bound, hpairCount]

/-- Fixed-degree polynomial covers are, in particular, square-
subexponential. -/
theorem hasSubexponentialEvaluationCovers_of_polynomialEvaluationCovers
    {X Y : Type*} [Norm X] [Norm Y] {value : X → Y → ℝ}
    (hcovers : HasPolynomialPowersetEvaluationCoversOnNormBalls value) :
    HasSubexponentialPowersetEvaluationCoversOnNormBalls value := by
  intro R_x R_y radius hradius
  obtain ⟨C, d, hcovers⟩ := hcovers R_x R_y radius hradius
  let bound : ℕ → ℕ := fun n ↦ C * (n + 1) ^ d
  refine ⟨bound, ?_, ?_⟩
  · have hsmall := eventually_polynomial_lt_two_pow (C ^ 2) (d + d)
    filter_upwards [hsmall] with n hn
    dsimp [bound]
    calc
      (C * (n + 1) ^ d) ^ 2 = C ^ 2 * (n + 1) ^ (d + d) := by
        rw [mul_pow, pow_add]
        ring
      _ < 2 ^ n := hn
  · intro n rows hrows parameters
    obtain ⟨centers, hcover, hcard⟩ :=
      hcovers n rows hrows parameters
    exact ⟨centers, hcover, hcard⟩

/-- The exact entropy form of Euclidean connective closure: subexponential
finite-sample covers of each coordinate class contradict the `2^n` separated
evaluations supplied by an IP pattern. -/
theorem euclideanConnective_isBoundedLocalNIP_of_subexponentialEvaluationCovers
    {X Y : Type*} [Norm X] [Norm Y] {f g : X → Y → ℝ}
    (hfCovers : HasSubexponentialPowersetEvaluationCoversOnNormBalls f)
    (hgCovers : HasSubexponentialPowersetEvaluationCoversOnNormBalls g) :
    IsBoundedLocalNIP fun x y ↦ euclideanConnective (f x y) (g x y) := by
  intro R_x R_y low high hgap
  let separation : ℝ := (high - low) / Real.sqrt 2
  let radius : ℝ := separation / 3
  have hseparation : 0 < separation := by
    dsimp [separation]
    exact div_pos (sub_pos.mpr hgap) (Real.sqrt_pos.2 (by norm_num))
  have hradius : 0 < radius := by
    dsimp [radius]
    positivity
  obtain ⟨fBound, hfSmall, hfCovers⟩ :=
    hfCovers R_x R_y radius hradius
  obtain ⟨gBound, hgSmall, hgCovers⟩ :=
    hgCovers R_x R_y radius hradius
  have hmaxSmall : ∀ᶠ n : ℕ in Filter.atTop,
      (max (fBound n) (gBound n)) ^ 2 < 2 ^ n := by
    filter_upwards [hfSmall, hgSmall] with n hfn hgn
    by_cases hle : fBound n ≤ gBound n
    · simpa [max_eq_right hle] using hgn
    · have hle' : gBound n ≤ fBound n := Nat.le_of_not_ge hle
      simpa [max_eq_left hle'] using hfn
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hmaxSmall
  refine ⟨N, ?_⟩
  intro n rows hrows hip
  by_contra hn
  have hNle : N ≤ n := Nat.le_of_not_gt hn
  have hip' : IsIPPattern
      (fun (i : Fin n) (parameter : ClosedNormBall Y R_y) ↦
        euclideanConnective
          (f (rows i) parameter.1) (g (rows i) parameter.1))
      low high := by
    simpa [boundedBinaryValue] using hip
  obtain ⟨parameters, hparameters⟩ :=
    hip'.exists_pairEvaluations_coordinateSeparated hgap
  obtain ⟨fCenters, hfCover, hfCard⟩ :=
    hfCovers n rows hrows parameters
  obtain ⟨gCenters, hgCover, hgCard⟩ :=
    hgCovers n rows hrows parameters
  have htwo : 2 ^ n ≤ fCenters.card * gCenters.card := by
    apply two_pow_le_mul_card_of_powerset_coordinateSeparated_of_supCovers
      (f := fun row parameter ↦ f (rows row) parameter.1)
      (g := fun row parameter ↦ g (rows row) parameter.1)
      (radius := radius) parameters hfCover hgCover
    intro S T hST
    obtain ⟨row, hrow⟩ := hparameters S T hST
    refine ⟨row, ?_⟩
    exact (show radius + radius ≤ separation by
      dsimp [radius]
      linarith).trans hrow
  have hcoverCard : fCenters.card * gCenters.card ≤
      (max (fBound n) (gBound n)) ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul
      (hfCard.trans (Nat.le_max_left _ _))
      (hgCard.trans (Nat.le_max_right _ _))
  exact (Nat.not_lt_of_ge (htwo.trans hcoverCard)) (hN n hNle)

/-- Unconditional finite-pattern closure for the Euclidean connective on
bounded norm balls. -/
theorem euclideanConnective_isBoundedLocalNIP
    {X Y : Type*} [Norm X] [Norm Y] {f g : X → Y → ℝ}
    (hfBounded : IsBoundedOnNormBalls f)
    (hgBounded : IsBoundedOnNormBalls g)
    (hfNIP : IsBoundedLocalNIP f)
    (hgNIP : IsBoundedLocalNIP g) :
    IsBoundedLocalNIP fun x y ↦
      euclideanConnective (f x y) (g x y) := by
  apply euclideanConnective_isBoundedLocalNIP_of_subexponentialEvaluationCovers
  · exact hasSubexponentialEvaluationCovers_of_boundedLocalNIP
      hfBounded hfNIP
  · exact hasSubexponentialEvaluationCovers_of_boundedLocalNIP
      hgBounded hgNIP

/-- The Euclidean connective satisfies the semantic closure interface with
no external premise. -/
theorem euclideanConnective_preservesBoundedLocalNIP₂ :
    PreservesBoundedLocalNIP₂ euclideanConnective := by
  intro X Y _ _ f g hfBounded hgBounded hfNIP hgNIP
  exact euclideanConnective_isBoundedLocalNIP
    hfBounded hgBounded hfNIP hgNIP

end NormFormula
