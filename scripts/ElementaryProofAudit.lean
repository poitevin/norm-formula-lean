import NormFormula.ModelTheory.AdditionalPaperClaims
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Check transitive proof dependencies, not just imported modules. The older
hyperplane results remain available as supplementary results, but none may
be used to prove the elementary count or the paper's fat-shattering theorem.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let roots := #[
    ``NormFormula.HalfGraph.exists_elementary_sparse_q_trace_cover,
    ``NormFormula.HalfGraph.exists_qTranslation_fatShattering_bound,
    ``NormFormula.hilbert_sparse_approximation_criterion,
    ``NormFormula.PaperClaims.y_unstable_and_fullBanachBallTheoryNIP,
    ``NormFormula.PaperClaims.additive_norm_conclusion,
    ``NormFormula.PaperClaims.main_theorem]
  let forbidden := #[
    "NormFormula.HalfGraph.hyperplaneFaceBound".toName,
    "NormFormula.HalfGraph.sparseTracePolynomialConstant".toName,
    "NormFormula.HalfGraph.abs_qSeminorm_add_sub_truncate_lt".toName,
    "NormFormula.HalfGraph.exists_truncation_error_bound".toName]
  let allowedAxioms := #[``propext, ``Classical.choice, ``Quot.sound]
  for root in roots do
    let (_, state) := ((Lean.CollectAxioms.collect root).run env).run {}
    for name in forbidden do
      if state.visited.contains name then
        throwError "{root} depends on the superseded argument: {name}"
    for name in state.axioms do
      unless allowedAxioms.contains name do
        throwError "{root} uses an unexpected axiom: {name}"
    logInfo m!"Elementary proof audit passed: {root}"
  let sparseTrace := ``NormFormula.HalfGraph.exists_elementary_sparse_q_trace_cover
  let (_, traceState) := ((Lean.CollectAxioms.collect sparseTrace).run env).run {}
  for name in #[``NormFormula.HalfGraph.qSeminorm_eq_max_finiteQValues_of_support_subset,
    ``NormFormula.HalfGraph.hasZeroBefore,
    ``NormFormula.HalfGraph.protectedIndexSet,
    ``NormFormula.HalfGraph.symbolicAffineQForm_elementary,
    ``NormFormula.HalfGraph.card_realizableRowThresholdTraces_le_elementary] do
    unless traceState.visited.contains name do
      throwError "{sparseTrace} does not use the required arXiv v2 argument: {name}"
  logInfo "Sparse-trace audit passed for the finite maximum, zero predecessors, protected initial segment, and elementary cut count."
  for root in #[``NormFormula.HalfGraph.exists_qTranslation_fatShattering_bound,
    ``NormFormula.PaperClaims.additive_norm_conclusion,
    ``NormFormula.PaperClaims.main_theorem] do
    let (_, state) := ((Lean.CollectAxioms.collect root).run env).run {}
    for name in #[``NormFormula.sparse_approximation_criterion,
      ``NormFormula.HalfGraph.exists_elementary_sparse_q_trace_cover,
      ``NormFormula.realCutPiece_eq_comparisons,
      ``NormFormula.HalfGraph.abs_qSeminorm_add_sub_truncate_le] do
      unless state.visited.contains name do
        throwError "{root} does not use the required paper argument: {name}"
  logInfo "The fat-shattering theorem, additive renorming corollary, and main theorem use the elementary count, non-strict truncation, and general criterion."

run_cmd do
  let env ← getEnv
  for root in #[``NormFormula.PaperClaims.main_theorem,
      ``NormFormula.PaperClaims.y_unstable_and_fullBanachBallTheoryNIP,
      ``NormFormula.PaperClaims.additive_norm_conclusion] do
    let (_, state) := ((Lean.CollectAxioms.collect root).run env).run {}
    for name in #[``NormFormula.ContinuousLogic.hilbertPredicate_representation,
        ``NormFormula.hilbert_norm_isStableOnBounded_separable,
        ``NormFormula.ContinuousLogic.MultiFormula.isNIPInCompleteTheory_connective,
        ``NormFormula.ContinuousLogic.hilbert_sparse_norm_isBoundedLocalNIP] do
      unless state.visited.contains name do
        throwError "{root} does not use the required Hilbert--seminorm argument: {name}"
    for name in #["NormFormula.hilbertNormTranslate_isBoundedLocalNIP".toName,
        "NormFormula.euclideanConnective_isBoundedLocalNIP".toName] do
      if state.visited.contains name then
        throwError "{root} still depends on the supplementary quantitative proof: {name}"
  for (root, required) in #[
      (``NormFormula.PaperClaims.x_positive_stable_and_fullBanachBallTheoryIP,
        ``NormFormula.l2Sum_norm_isStableOnBounded),
      (``NormFormula.XY.normAddMultiFormula_isNIPOnStructure,
        ``NormFormula.ContinuousLogic.normAddMultiFormula_isNIPOnStructure_l2Sum),
      (``NormFormula.X.positive_norm_ultrapower_hasInfiniteIPWitness,
        ``NormFormula.norm_hasInfiniteIPWitness_ultrapower_of_finitePatterns),
      (``NormFormula.XY.positive_norm_ultrapower_hasInfiniteIPWitness,
        ``NormFormula.norm_hasInfiniteIPWitness_ultrapower_of_finitePatterns),
      (``NormFormula.PaperClaims.exists_separable_hilbertian_ip_model,
        ``NormFormula.X.BallLanguage.XBallTheoryModel.normAddBallFormula_hasCompletedDistanceAddWitness_two),
      (``NormFormula.ContinuousLogic.l2_norm_stable_in_completeTheory,
        ``NormFormula.ContinuousLogic.hilbertPredicate_representation),
      (``NormFormula.ContinuousLogic.l2_norm_stable_in_completeTheory,
        ``NormFormula.hilbert_norm_isStableOnBounded),
      (``NormFormula.ContinuousLogic.l2_norm_stable_in_completeTheory,
        ``NormFormula.ContinuousLogic.ballSameCompleteTheory_mixedNormAddMultiStructure),
      (``NormFormula.XInfinity.predicateFreeNormAddFormula_hasIPInCompleteTheory,
        ``NormFormula.ContinuousLogic.BallFormula.finitePatternCompactness),
      (``NormFormula.XInfinity.predicateFreeNormAddFormula_hasIPInCompleteTheory,
        ``NormFormula.XInfinity.row_add_parameter)] do
    let (_, state) := ((Lean.CollectAxioms.collect root).run env).run {}
    unless state.visited.contains required do
      throwError "{root} does not use its general paper lemma: {required}"
  logInfo "Whole-paper proof audit passed: Hilbert stability in complete theories, finite connectives, general sums, arbitrary ultrafilters, radius-two witnesses, and XInfinity full-theory IP."
