# Paper claim correspondence

This ledger compares public Lean statements with the published TeX source
of [arXiv:2611.15930v2](https://arxiv.org/abs/2611.15930v2), revised
16 November 2026. The arXiv source fixes the statements and numbering used
here. The local v2 submission archive has earlier wording in the abstract,
introduction, and parts of Sections 4–6.

“Exact” means the statement has the paper's mathematical quantifiers and no
additional mathematical hypothesis. The general logical lemmas below are
specialized to the implemented languages; they do not formalize arbitrary
continuous signatures. Coordinate reindexing, normalized truth values, and
the precise language scopes are described below.
A build alone does not establish correspondence: the verification script
also audits axioms and transitive proof dependencies.

## Principal results

| Paper claim | Public Lean endpoint | Correspondence |
| --- | --- | --- |
| Theorems 1.1(i) and 3.3: stability in `X`, IP in its complete theory | `PaperClaims.x_positive_stable_and_fullBanachBallTheoryIP` | Exact; the public carrier is `XPositiveSpace`. Stability uses the general finite-dimensional-summand theorem. |
| Theorems 1.1(ii) and 4.7: instability in `Y`, complete-theory NIP | `PaperClaims.y_unstable_and_fullBanachBallTheoryNIP`; `HalfGraph.Y.predicateFreeNormAddFormula_isNIPInCompleteTheory_mixed` | Exact, at all independent nonnegative rational row and parameter radii, including zero. The NIP proof uses the general Hilbert–seminorm criterion. |
| Main geometric conclusions for `X,Y` | `PaperClaims.positive_geometric_conclusions`; `PaperClaims.main_theorem` | Exact: separability, midpoint constant `1/12`, uniform convexity, and Hilbert comparison constants `1,√3`. |
| Corollary 5.2: distinguished-space instability and NIP, complete-theory IP, IP in every free ultrapower, and geometry | `PaperClaims.xy_positive_unstable_ballNIP_and_fullBanachBallTheoryIP`; `PaperClaims.xy_positive_with_every_ultrapower`; `PaperClaims.positive_geometric_conclusions` | Exact for `XYPositiveSpace`; the arbitrary-ultrafilter witness retains the `√2` bounds and `√3,√6` thresholds. |
| Theorem 6.1: separable elementary extension `X ≺ W` with IP and the stated geometry | `PaperClaims.exists_separable_hilbertian_ip_model` | Exact. The source is `XPositiveSpace`; the same `W` has all conclusions. The public raw witness is in the `2`-ball, with thresholds `√3,√6`; the typed formula has radii `2,2` and thresholds `√3/8,√6/8`. |
| Theorem 1.1, as one conjunction | `PaperClaims.main_theorem` in `PositivePaperClaims.lean` | Exact for the positive-index presentation. The former zero-index statement is retained as `main_theorem_zeroBased`. |
| Table 1 and the abstract: separability, midpoint estimate, and `√3` distortion to `ℓ₂` for all five spaces | `PaperClaims.l2_table_geometry`; `X.positive_sqrtThree_isomorphic_l2`; `HalfGraph.y_sqrtThree_isomorphic_l2`; `XY.xy_positive_sqrtThree_isomorphic_l2`; `SeparableHilbertianNormAddIPModel.sqrtThree_isomorphic_l2` | The distortion conclusions bound the product of the operator norms of an equivalence to `HalfGraph.RealL2` and its inverse. The result for `W` applies to the same model package as the elementary extension. The other midpoint and separability conclusions appear in the main and direct-sum endpoints above. |

Names in tables are relative to `NormFormula`; `MultiFormula` and the
language constructions are in `NormFormula.ContinuousLogic`.

## General lemmas

| Paper item | Lean endpoint | Correspondence |
| --- | --- | --- |
| `lem:sequential-nip` | `MultiFormula.isNIPOnStructure_iff_pointwiseConvergentSubsequenceOnLocalType_general` | In the two-sorted `MultiFormula` language; no extra Lipschitz or separability premise. The proved pointwise dichotomy discharges BFT. |
| `lem:finite-pattern-transfer(i)` | `MultiFormula.sameTheory_and_infiniteWitness_every_free_ultrafilter` in `MultiCompactnessAlong.lean` | Any bounded many-predicate structure, any binary formula, and every `U : Ultrafilter ℕ` with `U ≤ atTop`; includes Łoś and the exact infinite witness. |
| Finite norm boxes in Banach ultrapowers | `norm_hasInfiniteIPWitness_ultrapower_of_finitePatterns` | Actual completed Banach ultrapower, every such `U`, exact original radii and thresholds. Specialized to positive-index `X` and `X ⊕₂ Y`. |
| `lem:finite-pattern-transfer(ii)` | `MultiFormula.hasFiniteIPPatternsInEveryDimension_of_sameTheory_infiniteWitness` | Exact thresholds and approximation in the two-sorted `MultiFormula` language. |
| `lem:nip-connectives` | `MultiFormula.isNIPInCompleteTheory_connective` | Arbitrary finite connective arity in the two-sorted `MultiFormula` language, after normalization to `[0,1]`; no global Lipschitz hypothesis. Also proved for distinguished structures. |
| `lem:uniform-convexity` | `uniformConvexSpaceOfMidpointEstimate`; augmented-norm and concrete midpoint theorems | Exact, with modulus `min 1 (ε²/12)`. |
| `lem:pythagoras` | `Analytic/L2SumPythagoras.lean`; `WeakL2Sum.lean` | Exact, for arbitrary finite-dimensional summands. |
| `thm:local-stability` | `l2Sum_norm_isStableOnBounded` in `L2SumStability.lean` | Exact for every sequence of finite-dimensional real normed spaces. No assumed weak compactness or uniform Hilbert distortion. Both `X` and `XInfinity.Space` use it. |
| `prop:hilbert-sparse-nip` | `augmentedSpace_fullTheoryNIP` in `AugmentedNormTheoryNIP.lean` | Arbitrary real Hilbert space, seminorm `p`, finite bound `p ≤ C‖·‖`, and fat-shattering bounds on each independently bounded pair of Hilbert balls. The actual quadratic normed carrier is complete by the displayed comparison. All independent rational ball radii are covered. |
| General norm reconstruction | `hilbert_sparse_norm_fullTheoryNIP` in `HilbertSparseNIP.lean` | A more general continuous-connective form, used by both the quadratic norm and `h+εq`. |
| `lem:expansion-transfer` | `MultiFormula.nip_reduct_of_expansion_of_bounds` | Predicate expansions in the two-sorted `MultiFormula` language; the bounded-structure wrapper discharges elementary-diagram compactness internally. The Hilbert–seminorm application also implements the finite-box reduct-transfer route. |
| `lem:local-nip-sum` | `normAddMultiFormula_isNIPOnStructure_l2Sum`; `normAddFixedMultiFormula_isNIPOnStructure_l2Sum` | Arbitrary normed real factors, hence all separable Banach factors in the paper; only distinguished-space NIP is assumed. Covers independent nonnegative radii. The concrete `XY` theorem uses the general result. |

The local direct-sum and finite-connective proofs use successive subsequences
on compact products of local profile spaces. This implements the role of
joint types without introducing a monster-model interface. The finite-connective
proof uses the proved BFT criterion instead of the paper's short indiscernible
argument; within the implemented language it has the same mathematical
hypotheses and conclusion.

`MultiFormula` has two fixed sorts, binary predicate symbols, finite continuous
connectives, and quantifiers over those two sorts. It is not a syntax for
arbitrary continuous languages with arbitrary functions, arities, and sorts.
The separate `BallFormula` syntax implements the standard rational Banach-ball
language, including terms and quantifiers over all its ball sorts. Proved
adapters give the paper's concrete full Banach-ball-theory conclusions; no
general translation from every continuous signature is claimed.

Arbitrary-ultrafilter Łoś and finite-pattern transfer are proved for
`MultiFormula`. Completed full `BallFormula` reduced products and their Łoś
theorem use the fixed `indexUltrafilter`. Separately, actual completed Banach
ultrapowers have the required norm witnesses for every free ultrafilter.
There is no general arbitrary-ultrafilter full-ball Łoś/identification theorem
connecting those two constructions. This scope limit does not weaken the
concrete norm-IP conclusions or the standard-language main theorem.

For general `ℓ₂`-sum stability, compactness of each finite-dimensional coordinate
ball supplies a coordinatewise convergent subsequence. A further subsequence
makes the norm defect converge. The general asymptotic Pythagoras theorem then
computes both iterated limits. This discharges the compactness needed for the
printed proof directly; the older weak-compactness interface remains available.

## Section 4.2 elementary proof

| Item | Lean endpoint | Correspondence |
| --- | --- | --- |
| Introduction and Section 4.1: `q(0,e₁) = 0` | `HalfGraph.qSeminorm_yVector_zero` | The first second-copy coordinate has no predecessor in the order. Lean index `0` corresponds to the paper's index `1`. |
| Equation (4.10) | `HalfGraph.abs_qSeminorm_add_sub_truncate_le` | Error at most `4η`, proved directly from coordinate estimates. |
| Proposition 4.2 | `hilbert_sparse_approximation_criterion`; `sparse_approximation_criterion` | Arbitrary Hilbert basis and nonnegative function; support bounds, uniform error tending to zero, real polynomial constants and exponents, independent nonnegative radii. The underlying result permits any support predicate. |
| Equation (4.12): finite maximum on sparse vectors | `HalfGraph.qSeminorm_eq_max_finiteQValues_of_support_subset`; `HalfGraph.protectedIndexSet` | The finite maximum collects pairs of retained coordinates, first-copy values with a later zero in the second copy, and second-copy values with an earlier zero in the first copy. The protected order data include the initial segment used to decide those earlier-zero cases. |
| Lemma 4.3 | `HalfGraph.exists_elementary_sparse_q_trace_cover` | Order types, distinct coordinate labels, singleton cuts and complementary intervals, and multiplication of counts give degree `2*k + k.choose 2`. Includes empty row sets and zero support bounds. |
| Theorem 4.4 | `HalfGraph.exists_qTranslation_fatShattering_bound` | Applies the general criterion to the elementary count and non-strict truncation estimate. |

`RealCutPartition.lean` counts `2|C|+1` singleton and interval pieces. The cut
set has at most `2n(m+1)^2` members, giving at most
`(4n(m+1)^2+1)^(k + k.choose 2)` traces per order type. Parameter labels record
both the copy and the numerical index. The existential multiplicative constant
need not equal a particular numerical choice in the article.

The old degree-`2k` hyperplane estimates remain supplementary. The proof audit
rejects their use and the former strict truncation argument in the elementary
count, fat-shattering, and both renorming results. It checks that the
sparse-trace theorem uses the finite maximum, earlier-zero test, protected
initial segment, and elementary count over the real cut partition.

## Section 4.3 proof route

`HilbertPredicateTransfer.lean` realizes the elementary diagram of an arbitrary
same-theory expansion model in a Hilbert ultrapower. Its named Hilbert
translation predicate is therefore represented by an actual Hilbert norm on
bounded vectors. `BanachUltrapower.lean` passes the parallelogram law through
the ultralimit and completion and constructs the inner product.

`HilbertStability.lean` proves norm stability in arbitrary real Hilbert spaces.
`hilbertPredicate_isStableInCompleteTheory` now explicitly transfers the
double-limit condition to every same-theory model of the bounded expansion.
`hilbert_norm_fullTheoryStable` transfers it through the mixed-radius reduct
to the full standard Banach-ball theory, including either zero radius;
`l2_norm_stable_in_completeTheory` is the Section 3.1 specialization.
`HilbertStableNIP.lean` obtains local NIP from the prepared weak-subsequence
calculation and the double-limit theorem. A putative infinite witness in a
nonseparable Hilbert space lies in the separable closed span of countably many
rows and finite-pattern parameters, so no separability hypothesis remains.

`HilbertSparseNIP.lean` transfers the seminorm's finite-pattern bounds, combines
the predicates with the general continuous-connective theorem, and transfers
the reconstruction identity. Finite-box compactness gives norm-pattern bounds
and the complete standard Banach-ball-theory conclusion. The public `Y` proof
uses this route. The dependency audit rejects its former quantitative Hilbert
finite-pattern estimate and Euclidean finite-cover closure proof.

The Hilbert realization uses an elementary diagram and a Hilbert ultrapower
rather than copying the paper's vector-operation reconstruction literally.
This is a concrete implementation of the transferred-Hilbert-norm step; its
NIP conclusion genuinely depends on the Hilbert stability theorem.

## Additional examples

| Paper item | Lean endpoint | Correspondence |
| --- | --- | --- |
| Corollary 4.8 (Bollobás's renorming) | `Bollobas.Space`; `Bollobas.half_graph`; `PaperClaims.additive_norm_conclusion` | Actual norm `h+εq` for every real `ε>0`; comparison constants `1,1+ε√2`; values `√2+2ε` and `√2+ε`; instability and complete-standard-ball-theory NIP. |
| Remark 6.2 | `DirectMembership.Space`; `PaperClaims.direct_membership_conclusion` | The specified membership seminorm, bound `p²≤2h²`, values `√3,√6`, and an infinite witness including the empty-set parameter. Separability, completeness, midpoint estimate, uniform convexity, `√3` Hilbert comparison, and exclusion of `c₀` hold in that carrier. |
| Section 3.3, `X_∞` | `XInfinity.norm_stable`; `finite_boxes`; `ultrapower_IP`; `c0Embedding`; `predicateFreeNormAddFormula_hasIPInCompleteTheory` | Positive-index `(⊕ ℓ∞ⁿ)₂`, `1,2` boxes, an explicit linear isometry of `c₀` into every free Banach ultrapower, and IP in the full standard Banach-ball theory. The last corollary uses unit-ball variables with normalized thresholds `1/4,1/2`. |
| Section 3.1 and the `ℓ₂` table row | `l2_stable_and_fullTheoryNIP`; `l2_norm_stable_in_completeTheory` | Norm stability on the space and in its complete standard Banach-ball theory, as well as complete-theory NIP. No assertion of formalizing stability of the entire Hilbert theory. |

The v2 discussion of Lupini's additive block norms, dense-order seminorm
`γ`, and NIP of the entire dense-order renorming theory is cited background.
The formalized examples in Table 1 are the paper's own spaces. The additive
result in the formalization concerns the norm formula for Bollobás's
ordered-pair seminorm `q` on natural-number coordinates.

## Presentations and retained compatibility endpoints

`XPositiveSpace` enumerates blocks of dimensions `1,2,…`. Internally,
`XSpace` includes the empty block at zero. `xSpaceEquivPositive` moves each
empty-subset coordinate to the next block and fixes the other coordinates;
the block seminorms ignore those empty-subset coordinates. Public main and
positive direct-sum statements use the paper's presentation. The old internal
endpoints remain available under their existing names.

`Y` uses zero-based coordinates, identified with the paper's indices by
`j ↦ j+1`. The direct membership space uses two copies of `ℓ₂`, with the second
copy reindexed by the bijection `DirectMembership.code : Finset ℕ ≃ ℕ`.
Its basis labels and admissible pairs are exactly those of the printed `V`.

`BanachUltrapower U E` is the separated completion of bounded families with
seminorm `lim_U ‖x_i‖`. The universal-ultrafilter norm witnesses are statements
about this normed carrier, separate from the language-level Łoś theorem.
The condition `U ≤ atTop` expresses nonprincipality on `ℕ`.

The `W` construction retains the diagonal copy of `X`, applies the proved
countable-language Tarski–Vaught construction, and reconstructs the complete
Banach carrier. The elementary embedding, norm IP witness, and geometry all
refer to that same carrier. The older radius-`4` lemmas remain compatibility
results; the public theorem uses the sharp radius-`2` landing result.

## Validation and scope

The required command is `bash scripts/verify_formalization.sh`. It builds the
umbrella library, rejects unfinished proof declarations and custom axioms,
audits every listed endpoint against `propext`, `Classical.choice`, and
`Quot.sound`, and checks the required transitive proof dependencies. The audit
includes all new general results, examples, positive-index endpoints, sharp
witness transfer, and literal `ℓ₂` isomorphisms.

Validation against arXiv v2 passed on 2026-11-21. The full build completed
2648 jobs, the kernel axiom audit passed for all 60 listed endpoints, and
the elementary and whole-paper proof dependency audits passed. These checks
cover the first-coordinate identity, the Table 1 geometry, and the elementary
sparse-trace argument used by both renormings. The source scan found no
unfinished proof declarations or custom axioms.

The scope treats the discussion of superreflexivity, superstability,
nondistortion, and stability of entire Hilbert theories as cited background.
The former `ModelTheory.XHilbertianIPModel` presentation remains a labelled
legacy interface, not evidence for the public claims. Different standard
background proofs, such as the direct Hilbert sign-sum argument excluding
`c₀`, remain permissible implementation choices and require no article edits.
