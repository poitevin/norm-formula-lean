# The norm formula in a Banach space and in its complete theory

Lean 4 formalization of Pedro Poitevin's paper. This version corresponds to
the revision published on arXiv on 16 November 2026. [arXiv:2611.15930v2](https://arxiv.org/abs/2611.15930v2)

## What Lean checks

| Result in the paper | Lean declaration |
| --- | --- |
| Theorem 1.1. The spaces `X`, `Y`, and the separable elementary extension `W` | [`PaperClaims.main_theorem`](NormFormula/ModelTheory/PositivePaperClaims.lean) |
| Lemma 4.3 and Theorem 4.4. The sparse threshold count and fat-shattering bound for `q` | [`HalfGraph.exists_elementary_sparse_q_trace_cover`](NormFormula/Combinatorics/ElementarySparseTrace.lean), [`HalfGraph.exists_qTranslation_fatShattering_bound`](NormFormula/Combinatorics/QFatShattering.lean) |
| Corollary 4.8. Instability and complete-theory NIP of the norm formula for every positive coefficient in Bollobás's additive renorming | [`PaperClaims.additive_norm_conclusion`](NormFormula/ModelTheory/AdditionalPaperClaims.lean) |
| Corollary 5.2. Local NIP, instability, and complete-theory IP for `X ⊕₂ Y` | [`PaperClaims.xy_positive_unstable_ballNIP_and_fullBanachBallTheoryIP`](NormFormula/ModelTheory/PositivePaperClaims.lean) |
| Table 1. Distortion at most `√3` to standard real `ℓ₂` for all five examples | [Quantitative isomorphisms](NormFormula/ModelTheory/L2Isomorphisms.lean) |

The correspondence ledger gives the declarations for the remaining results,
including the geometry of `W` and IP in every free ultrapower of `X ⊕₂ Y`.
It records the scope of the general continuous-logic lemmas and the concrete
conclusions in the standard rational Banach-ball language.
[Paper claim correspondence](PAPER_CLAIM_CORRESPONDENCE.md)

## Reproduce the verification

With Elan, Git, Bash, and ripgrep installed, run these commands from the
repository root. The first downloads the Mathlib build cache to save time.

```sh
lake exe cache get
bash scripts/verify_formalization.sh
lake env leanchecker --fresh NormFormula
```

`lean-toolchain` pins Lean 4.29.1, and `lake-manifest.json` records the exact
Mathlib and transitive dependency revisions. The verification script builds
the project, checks for unfinished proof declarations and custom axioms,
and audits 60 declarations. Their transitive axiom dependencies are confined
to `propext`, `Classical.choice`, and `Quot.sound`. The proof dependency audit
also checks that the two renorming results use the paper's elementary
sparse-trace argument. The final command replays the declarations in a fresh
kernel environment. [Lean proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)

## License

The Lean formalization is available under the
[Apache License, Version 2.0](LICENSE).
