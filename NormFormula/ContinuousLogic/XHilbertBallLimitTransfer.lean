import NormFormula.ContinuousLogic.BanachBallTarskiVaught
import NormFormula.ContinuousLogic.XHilbertBallReductHilbert
import NormFormula.ContinuousLogic.XHilbertBallSentences

/-!
# Geometric sentence transfer to the closed witness-limit sorts

The unrestricted Tarski--Vaught theorem gives equality of complete typed
ball theories in the direction from the closed limit to the ambient
`XSpace` expansion.  The sentence-transfer theorems use the reverse
orientation, which is obtained by symmetry here.  We then specialize the
comparison, parallelogram, and midpoint consequences to the actual closed
limit carriers.
-/

namespace NormFormula.X.BallLanguage

noncomputable section

open NormFormula.ContinuousLogic

/-- The distinguished `XSpace` expansion and its closed witness limit have
the same complete typed ball theory, in the orientation used by transfer. -/
theorem expansionStructure_sameCompleteTheory_limitBallStructure
    (initial : BallWitnessIndexing expansionStructure) :
    BallSameCompleteTheory expansionStructure initial.limitBallStructure :=
  fun sentence ↦
    (initial.limitBallStructure_sameCompleteTheory_ambient sentence).symm

/-- Elementary transfer of the two auxiliary-Hilbert norm comparisons to
every point of every closed rational-radius limit carrier. -/
theorem limitCarrier_comparisons_of_elementarity
    (initial : BallWitnessIndexing expansionStructure)
    (radius : ℚ≥0) (point : initial.LimitCarrier radius) :
    ((hilbertNormFormula (unaryVariable radius)).realize
        initial.limitBallStructure
        (Fin.cons point (fun i : Fin 0 ↦ nomatch i)) : ℝ) ≤
      ((ambientNormFormula (unaryVariable radius)).realize
        initial.limitBallStructure
        (Fin.cons point (fun i : Fin 0 ↦ nomatch i)) : ℝ) ∧
    ((ambientNormFormula (unaryVariable radius)).realize
        initial.limitBallStructure
        (Fin.cons point (fun i : Fin 0 ↦ nomatch i)) : ℝ) ≤
      Real.sqrt 3 *
        ((hilbertNormFormula (unaryVariable radius)).realize
          initial.limitBallStructure
          (Fin.cons point (fun i : Fin 0 ↦ nomatch i)) : ℝ) :=
  comparisons_of_sameCompleteTheory initial.limitBallStructure
    (expansionStructure_sameCompleteTheory_limitBallStructure initial)
    radius point

/-- Elementary transfer of the auxiliary-Hilbert parallelogram identity to
every pair in one closed rational-radius limit carrier. -/
theorem limitCarrier_parallelogram_of_elementarity
    (initial : BallWitnessIndexing expansionStructure)
    (radius : ℚ≥0) (x y : initial.LimitCarrier radius) :
    rationalBallMetricBound (radius + radius) ^ 2 *
        (((hilbertAddFormula radius).realize initial.limitBallStructure
            (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) : ℝ) ^ 2 +
          ((hilbertSubFormula radius).realize initial.limitBallStructure
            (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) : ℝ) ^ 2) =
      2 * rationalBallMetricBound radius ^ 2 *
        (((hilbertFirstFormula radius).realize initial.limitBallStructure
            (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) : ℝ) ^ 2 +
          ((hilbertSecondFormula radius).realize initial.limitBallStructure
            (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) : ℝ) ^ 2) :=
  parallelogram_of_sameCompleteTheory initial.limitBallStructure
    (expansionStructure_sameCompleteTheory_limitBallStructure initial)
    radius x y

/-- Elementary transfer of the paper's fixed midpoint sentence to the closed
unit-radius limit carrier. -/
theorem limitCarrier_midpoint_of_elementarity
    (initial : BallWitnessIndexing expansionStructure)
    (x y : initial.LimitCarrier (1 : ℚ≥0)) :
    4 * (ambientAddUnitFormula.realize initial.limitBallStructure
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) : ℝ) ^ 2 +
      (4 / 3 : ℝ) *
        (ambientSubUnitFormula.realize initial.limitBallStructure
          (Fin.cons x (Fin.cons y (fun i : Fin 0 ↦ nomatch i))) : ℝ) ^ 2 ≤
      1 :=
  midpoint_of_sameCompleteTheory initial.limitBallStructure
    (expansionStructure_sameCompleteTheory_limitBallStructure initial) x y

end

end NormFormula.X.BallLanguage
