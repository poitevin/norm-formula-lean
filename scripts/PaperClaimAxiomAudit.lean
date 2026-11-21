import NormFormula.ModelTheory.AdditionalPaperClaims
import NormFormula.ModelTheory.L2Isomorphisms
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
This file is run by `verify_formalization.sh`.  It makes the kernel dependency
audit for every public principal endpoint reproducible in the build log.
The project-wide source scan separately rejects `sorry`, `admit`, and custom
`axiom` declarations.
-/

#print axioms NormFormula.PaperClaims.x_stable_and_fullBanachBallTheoryIP
#print axioms NormFormula.PaperClaims.y_unstable_and_fullBanachBallTheoryNIP
#print axioms NormFormula.HalfGraph.Y.predicateFreeNormAddFormula_isNIPInCompleteTheory_mixed
#print axioms NormFormula.PaperClaims.xy_unstable_ballNIP_and_fullBanachBallTheoryIP
#print axioms NormFormula.PaperClaims.concrete_normFormula_NIP_on_arbitrary_fixed_balls
#print axioms NormFormula.PaperClaims.concrete_geometric_conclusions
#print axioms NormFormula.X.BallLanguage.XBallTheoryModel.standardCompletedDirectedPoint_sameCompleteTheory
#print axioms NormFormula.X.BallLanguage.XBallTheoryModel.predicateFreeNormAddFormula_hasInfiniteIPWitness_of_completed
#print axioms NormFormula.X.xSpaceEquivPositive
#print axioms NormFormula.PaperClaims.exists_separable_hilbertian_ip_model
#print axioms NormFormula.PaperClaims.main_theorem

#print axioms NormFormula.HalfGraph.exists_elementary_sparse_q_trace_cover
#print axioms NormFormula.HalfGraph.abs_qSeminorm_add_sub_truncate_le
#print axioms NormFormula.sparse_approximation_criterion
#print axioms NormFormula.hilbert_sparse_approximation_criterion
#print axioms NormFormula.HalfGraph.exists_qTranslation_fatShattering_bound

#print axioms NormFormula.PaperClaims.x_positive_stable_and_fullBanachBallTheoryIP
#print axioms NormFormula.PaperClaims.xy_positive_unstable_ballNIP_and_fullBanachBallTheoryIP
#print axioms NormFormula.PaperClaims.positive_geometric_conclusions
#print axioms NormFormula.PaperClaims.xy_positive_with_every_ultrapower
#print axioms NormFormula.PaperClaims.additive_norm_conclusion
#print axioms NormFormula.PaperClaims.direct_membership_conclusion
#print axioms NormFormula.ContinuousLogic.MultiFormula.isNIPOnStructure_iff_pointwiseConvergentSubsequenceOnLocalType_general
#print axioms NormFormula.ContinuousLogic.MultiFormula.isNIPInCompleteTheory_connective
#print axioms NormFormula.ContinuousLogic.MultiFormula.nip_reduct_of_expansion_of_bounds
#print axioms NormFormula.l2Sum_norm_isStableOnBounded
#print axioms NormFormula.hilbert_norm_isStableOnBounded
#print axioms NormFormula.ContinuousLogic.normAddMultiFormula_isNIPOnStructure_l2Sum
#print axioms NormFormula.normAddFixedMultiFormula_isNIPOnStructure_l2Sum
#print axioms NormFormula.ContinuousLogic.hilbertPredicate_representation
#print axioms NormFormula.ContinuousLogic.hilbertPredicate_isNIPInCompleteTheory
#print axioms NormFormula.ContinuousLogic.augmentedSpace_fullTheoryNIP
#print axioms NormFormula.ContinuousLogic.hilbert_sparse_norm_fullTheoryNIP
#print axioms NormFormula.ContinuousLogic.MultiFormula.sameTheory_and_infiniteWitness_every_free_ultrafilter
#print axioms NormFormula.norm_hasInfiniteIPWitness_ultrapower_of_finitePatterns
#print axioms NormFormula.X.positive_norm_ultrapower_hasInfiniteIPWitness
#print axioms NormFormula.XY.positive_norm_ultrapower_hasInfiniteIPWitness
#print axioms NormFormula.XInfinity.norm_stable
#print axioms NormFormula.XInfinity.finite_boxes
#print axioms NormFormula.XInfinity.c0Embedding
#print axioms NormFormula.XInfinity.ultrapower_IP
#print axioms NormFormula.Bollobas.half_graph
#print axioms NormFormula.DirectMembership.norm_row_add_parameter
#print axioms NormFormula.ContinuousLogic.l2_stable_and_fullTheoryNIP
#print axioms NormFormula.X.positive_isomorphic_l2
#print axioms NormFormula.HalfGraph.y_isomorphic_l2
#print axioms NormFormula.XY.xy_positive_isomorphic_l2
#print axioms NormFormula.X.BallLanguage.SeparableHilbertianNormAddIPModel.isomorphic_l2
#print axioms NormFormula.X.BallLanguage.XBallTheoryModel.predicateFreeNormAddFormula_hasInfiniteIPWitness_of_completed_two
#print axioms NormFormula.ContinuousLogic.hilbertPredicate_isStableInCompleteTheory
#print axioms NormFormula.ContinuousLogic.hilbert_norm_fullTheoryStable
#print axioms NormFormula.ContinuousLogic.l2_norm_stable_in_completeTheory
#print axioms NormFormula.XInfinity.predicateFreeNormAddFormula_hasFiniteIPPatternsInEveryDimension
#print axioms NormFormula.XInfinity.predicateFreeNormAddFormula_hasIPInCompleteTheory
#print axioms NormFormula.HalfGraph.qSeminorm_yVector_zero
#print axioms NormFormula.PaperClaims.l2_table_geometry
#print axioms NormFormula.X.positive_sqrtThree_isomorphic_l2
#print axioms NormFormula.HalfGraph.y_sqrtThree_isomorphic_l2
#print axioms NormFormula.XY.xy_positive_sqrtThree_isomorphic_l2
#print axioms NormFormula.X.BallLanguage.SeparableHilbertianNormAddIPModel.sqrtThree_isomorphic_l2

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let roots := #[
    ``NormFormula.PaperClaims.x_stable_and_fullBanachBallTheoryIP,
    ``NormFormula.PaperClaims.y_unstable_and_fullBanachBallTheoryNIP,
    ``NormFormula.HalfGraph.Y.predicateFreeNormAddFormula_isNIPInCompleteTheory_mixed,
    ``NormFormula.PaperClaims.xy_unstable_ballNIP_and_fullBanachBallTheoryIP,
    ``NormFormula.PaperClaims.concrete_normFormula_NIP_on_arbitrary_fixed_balls,
    ``NormFormula.PaperClaims.concrete_geometric_conclusions,
    ``NormFormula.X.BallLanguage.XBallTheoryModel.standardCompletedDirectedPoint_sameCompleteTheory,
    ``NormFormula.X.BallLanguage.XBallTheoryModel.predicateFreeNormAddFormula_hasInfiniteIPWitness_of_completed,
    ``NormFormula.X.xSpaceEquivPositive,
    ``NormFormula.PaperClaims.exists_separable_hilbertian_ip_model,
    ``NormFormula.PaperClaims.main_theorem,
    ``NormFormula.HalfGraph.exists_elementary_sparse_q_trace_cover,
    ``NormFormula.HalfGraph.abs_qSeminorm_add_sub_truncate_le,
    ``NormFormula.sparse_approximation_criterion,
    ``NormFormula.hilbert_sparse_approximation_criterion,
    ``NormFormula.HalfGraph.exists_qTranslation_fatShattering_bound,
    ``NormFormula.PaperClaims.x_positive_stable_and_fullBanachBallTheoryIP,
    ``NormFormula.PaperClaims.xy_positive_unstable_ballNIP_and_fullBanachBallTheoryIP,
    ``NormFormula.PaperClaims.positive_geometric_conclusions,
    ``NormFormula.PaperClaims.xy_positive_with_every_ultrapower,
    ``NormFormula.PaperClaims.additive_norm_conclusion,
    ``NormFormula.PaperClaims.direct_membership_conclusion,
    ``NormFormula.ContinuousLogic.MultiFormula.isNIPOnStructure_iff_pointwiseConvergentSubsequenceOnLocalType_general,
    ``NormFormula.ContinuousLogic.MultiFormula.isNIPInCompleteTheory_connective,
    ``NormFormula.ContinuousLogic.MultiFormula.nip_reduct_of_expansion_of_bounds,
    ``NormFormula.l2Sum_norm_isStableOnBounded,
    ``NormFormula.hilbert_norm_isStableOnBounded,
    ``NormFormula.ContinuousLogic.normAddMultiFormula_isNIPOnStructure_l2Sum,
    ``NormFormula.normAddFixedMultiFormula_isNIPOnStructure_l2Sum,
    ``NormFormula.ContinuousLogic.hilbertPredicate_representation,
    ``NormFormula.ContinuousLogic.hilbertPredicate_isNIPInCompleteTheory,
    ``NormFormula.ContinuousLogic.augmentedSpace_fullTheoryNIP,
    ``NormFormula.ContinuousLogic.hilbert_sparse_norm_fullTheoryNIP,
    ``NormFormula.ContinuousLogic.MultiFormula.sameTheory_and_infiniteWitness_every_free_ultrafilter,
    ``NormFormula.norm_hasInfiniteIPWitness_ultrapower_of_finitePatterns,
    ``NormFormula.X.positive_norm_ultrapower_hasInfiniteIPWitness,
    ``NormFormula.XY.positive_norm_ultrapower_hasInfiniteIPWitness,
    ``NormFormula.XInfinity.norm_stable,
    ``NormFormula.XInfinity.finite_boxes,
    ``NormFormula.XInfinity.c0Embedding,
    ``NormFormula.XInfinity.ultrapower_IP,
    ``NormFormula.Bollobas.half_graph,
    ``NormFormula.DirectMembership.norm_row_add_parameter,
    ``NormFormula.ContinuousLogic.l2_stable_and_fullTheoryNIP,
    ``NormFormula.X.positive_isomorphic_l2,
    ``NormFormula.HalfGraph.y_isomorphic_l2,
    ``NormFormula.XY.xy_positive_isomorphic_l2,
    ``NormFormula.X.BallLanguage.SeparableHilbertianNormAddIPModel.isomorphic_l2,
    ``NormFormula.X.BallLanguage.XBallTheoryModel.predicateFreeNormAddFormula_hasInfiniteIPWitness_of_completed_two,
    ``NormFormula.ContinuousLogic.hilbertPredicate_isStableInCompleteTheory,
    ``NormFormula.ContinuousLogic.hilbert_norm_fullTheoryStable,
    ``NormFormula.ContinuousLogic.l2_norm_stable_in_completeTheory,
    ``NormFormula.XInfinity.predicateFreeNormAddFormula_hasFiniteIPPatternsInEveryDimension,
    ``NormFormula.XInfinity.predicateFreeNormAddFormula_hasIPInCompleteTheory,
    ``NormFormula.HalfGraph.qSeminorm_yVector_zero,
    ``NormFormula.PaperClaims.l2_table_geometry,
    ``NormFormula.X.positive_sqrtThree_isomorphic_l2,
    ``NormFormula.HalfGraph.y_sqrtThree_isomorphic_l2,
    ``NormFormula.XY.xy_positive_sqrtThree_isomorphic_l2,
    ``NormFormula.X.BallLanguage.SeparableHilbertianNormAddIPModel.sqrtThree_isomorphic_l2]
  for root in roots do
    let (_, state) := ((Lean.CollectAxioms.collect root).run env).run {}
    for name in state.axioms do
      unless allowed.contains name do
        throwError "Unexpected axiom in {root}: {name}"
  logInfo m!"Kernel audit passed for {roots.size} endpoints."
