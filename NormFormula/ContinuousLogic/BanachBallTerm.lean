import NormFormula.ContinuousLogic.BanachBallSystem

/-!
# Typed terms for rational-radius Banach balls

Terms are indexed by a finite context of ball radii and by their output
radius.  Their constructors are exactly the function symbols of the standard
ball-sorted Banach language: inclusions, zero, negation, addition, and
rational scalar multiplication.

Every term evaluates in any `RationalBallSystem`.  The radius indices make
every operation type-correct, and structural induction proves that every
term denotes a uniformly continuous function of its assignment.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

open scoped Topology

/-- A finite context assigns a rational ball radius to each free variable. -/
abbrev BallContext (n : ℕ) := Fin n → ℚ≥0

/-- Radius-indexed terms in the rational ball-sorted Banach language. -/
inductive BallTerm {n : ℕ} (context : BallContext n) : ℚ≥0 → Type
  | variable (i : Fin n) : BallTerm context (context i)
  | inclusion {r s : ℚ≥0} (h : r ≤ s) :
      BallTerm context r → BallTerm context s
  | zero (r : ℚ≥0) : BallTerm context r
  | neg {r : ℚ≥0} : BallTerm context r → BallTerm context r
  | add {r s : ℚ≥0} :
      BallTerm context r → BallTerm context s → BallTerm context (r + s)
  | smul (q : ℚ) {r : ℚ≥0} :
      BallTerm context r → BallTerm context (q.nnabs * r)

namespace BallTerm

universe u

/-- A typed assignment of the variables in a ball context. -/
abbrev Assignment (S : RationalBallSystem.{u}) {n : ℕ}
    (context : BallContext n) :=
  ∀ i : Fin n, S.Ball (context i)

/-- Evaluation of a typed term in a rational ball system. -/
def realize (S : RationalBallSystem.{u}) {n : ℕ}
    {context : BallContext n} {r : ℚ≥0} :
    BallTerm context r → Assignment S context → S.Ball r
  | .variable i, assignment => assignment i
  | .inclusion h term, assignment =>
      S.inclusion h (term.realize S assignment)
  | .zero radius, _assignment => S.zero radius
  | .neg term, assignment => S.neg _ (term.realize S assignment)
  | .add left right, assignment =>
      S.add _ _ (left.realize S assignment, right.realize S assignment)
  | .smul q term, assignment => S.smul q _ (term.realize S assignment)

@[simp]
theorem realize_variable (S : RationalBallSystem.{u}) {n : ℕ}
    {context : BallContext n} (i : Fin n)
    (assignment : Assignment S context) :
    (BallTerm.variable i).realize S assignment = assignment i :=
  rfl

@[simp]
theorem realize_inclusion (S : RationalBallSystem.{u}) {n : ℕ}
    {context : BallContext n} {r s : ℚ≥0} (h : r ≤ s)
    (term : BallTerm context r) (assignment : Assignment S context) :
    (BallTerm.inclusion h term).realize S assignment =
      S.inclusion h (term.realize S assignment) :=
  rfl

@[simp]
theorem realize_zero (S : RationalBallSystem.{u}) {n : ℕ}
    {context : BallContext n} (r : ℚ≥0)
    (assignment : Assignment S context) :
    (BallTerm.zero r).realize S assignment = S.zero r :=
  rfl

@[simp]
theorem realize_neg (S : RationalBallSystem.{u}) {n : ℕ}
    {context : BallContext n} {r : ℚ≥0}
    (term : BallTerm context r) (assignment : Assignment S context) :
    (BallTerm.neg term).realize S assignment =
      S.neg r (term.realize S assignment) :=
  rfl

@[simp]
theorem realize_add (S : RationalBallSystem.{u}) {n : ℕ}
    {context : BallContext n} {r s : ℚ≥0}
    (left : BallTerm context r) (right : BallTerm context s)
    (assignment : Assignment S context) :
    (BallTerm.add left right).realize S assignment =
      S.add r s (left.realize S assignment, right.realize S assignment) :=
  rfl

@[simp]
theorem realize_smul (S : RationalBallSystem.{u}) {n : ℕ}
    {context : BallContext n} (q : ℚ) {r : ℚ≥0}
    (term : BallTerm context r) (assignment : Assignment S context) :
    (BallTerm.smul q term).realize S assignment =
      S.smul q r (term.realize S assignment) :=
  rfl

/-- Every typed term denotes a uniformly continuous function of its finite
assignment. -/
theorem realize_uniformContinuous (S : RationalBallSystem.{u})
    {n : ℕ} {context : BallContext n} {r : ℚ≥0}
    (term : BallTerm context r) :
    UniformContinuous (term.realize S) := by
  induction term with
  | «variable» i =>
      exact Pi.uniformContinuous_proj (fun j : Fin n ↦ S.Ball (context j)) i
  | inclusion h term induction =>
      exact (S.inclusion_uniformContinuous h).comp induction
  | zero radius =>
      exact uniformContinuous_const
  | neg term induction =>
      exact (S.neg_uniformContinuous _).comp induction
  | add left right leftInduction rightInduction =>
      exact (S.add_uniformContinuous _ _).comp
        (leftInduction.prodMk rightInduction)
  | smul q term induction =>
      exact (S.smul_uniformContinuous q _).comp induction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- The ambient vector represented by a term evaluated in the standard ball
system of a Banach space. -/
def standardValue {n : ℕ} {context : BallContext n} {r : ℚ≥0}
    (term : BallTerm context r)
    (assignment : Assignment (standardRationalBallSystem (E := E)) context) : E :=
  (term.realize (standardRationalBallSystem (E := E)) assignment).1

@[simp]
theorem standardValue_variable {n : ℕ} {context : BallContext n}
    (i : Fin n)
    (assignment : Assignment (standardRationalBallSystem (E := E)) context) :
    (BallTerm.variable i).standardValue assignment = (assignment i).1 :=
  rfl

@[simp]
theorem standardValue_inclusion {n : ℕ} {context : BallContext n}
    {r s : ℚ≥0} (h : r ≤ s) (term : BallTerm context r)
    (assignment : Assignment (standardRationalBallSystem (E := E)) context) :
    (BallTerm.inclusion h term).standardValue assignment =
      term.standardValue assignment :=
  rfl

@[simp]
theorem standardValue_zero {n : ℕ} {context : BallContext n} (r : ℚ≥0)
    (assignment : Assignment (standardRationalBallSystem (E := E)) context) :
    (BallTerm.zero r).standardValue assignment = 0 :=
  rfl

@[simp]
theorem standardValue_neg {n : ℕ} {context : BallContext n} {r : ℚ≥0}
    (term : BallTerm context r)
    (assignment : Assignment (standardRationalBallSystem (E := E)) context) :
    (BallTerm.neg term).standardValue assignment =
      -term.standardValue assignment :=
  rfl

@[simp]
theorem standardValue_add {n : ℕ} {context : BallContext n}
    {r s : ℚ≥0} (left : BallTerm context r) (right : BallTerm context s)
    (assignment : Assignment (standardRationalBallSystem (E := E)) context) :
    (BallTerm.add left right).standardValue assignment =
      left.standardValue assignment + right.standardValue assignment :=
  rfl

@[simp]
theorem standardValue_smul {n : ℕ} {context : BallContext n}
    (q : ℚ) {r : ℚ≥0} (term : BallTerm context r)
    (assignment : Assignment (standardRationalBallSystem (E := E)) context) :
    (BallTerm.smul q term).standardValue assignment =
      (q : ℝ) • term.standardValue assignment :=
  rfl

/-- The canonical typed term for addition of two variables from radii `r`
and `s`. -/
def binaryAddTerm (r s : ℚ≥0) :
    BallTerm (![r, s] : BallContext 2) (r + s) :=
  .add (.variable 0) (.variable 1)

/-- The canonical typed term for the difference of two variables with the
same radius. -/
def binarySubTerm (r : ℚ≥0) :
    BallTerm (![r, r] : BallContext 2) (r + r) :=
  .add (.variable 0) (.neg (.variable 1))

@[simp]
theorem binaryAddTerm_standardValue (r s : ℚ≥0)
    (assignment : Assignment (standardRationalBallSystem (E := E))
      (![r, s] : BallContext 2)) :
    (binaryAddTerm r s).standardValue assignment =
      (assignment 0).1 + (assignment 1).1 :=
  rfl

@[simp]
theorem binarySubTerm_standardValue (r : ℚ≥0)
    (assignment : Assignment (standardRationalBallSystem (E := E))
      (![r, r] : BallContext 2)) :
    (binarySubTerm r).standardValue assignment =
      (assignment 0).1 - (assignment 1).1 := by
  simp [binarySubTerm, standardValue, realize, standardRationalBallSystem,
    rationalBallAdd, rationalBallNeg, sub_eq_add_neg]

end BallTerm

end

end NormFormula.ContinuousLogic
