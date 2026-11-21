import NormFormula.ContinuousLogic.MultiPredicate

/-!
# Theory-level IP and NIP for many-predicate formulae

This file gives the many-predicate language its semantic complete-theory
notions of IP and NIP.  It then proves that formulae equivalent throughout a
complete theory have exactly the same IP and NIP status.  The one-way NIP
corollary is the `nip_of_equivalent` principle required by the abstract
`ContinuousNIPSemantics` interface.
-/

namespace NormFormula.ContinuousLogic

noncomputable section

universe u v w z

namespace MultiStructure

/-- A formula-preserving embedding of a reduct model into the reduct of a
model of the complete expansion theory.  This is the semantic output of the
standard elementary-diagram/compactness argument. -/
structure SameTheoryReductEmbedding
    {Symbol : Type w} {Target : Type z}
    (f : Symbol → Target) (M : MultiStructure.{u, v, z} Target)
    (N : MultiStructure.{u, v, w} Symbol) where
  expansion : MultiStructure.{u, v, z} Target
  sameTheory : MultiSameCompleteTheory M expansion
  rowMap : N.Row → expansion.Row
  parameterMap : N.Parameter → expansion.Parameter
  realize_reduct : ∀ {rowVars parameterVars : ℕ}
    (φ : MultiFormula Symbol rowVars parameterVars)
    (rows : Fin rowVars → N.Row)
    (parameters : Fin parameterVars → N.Parameter),
    (φ.map f).realize expansion (fun i ↦ rowMap (rows i))
        (fun j ↦ parameterMap (parameters j)) =
      φ.realize N rows parameters

/-- The exact model-theoretic lifting property needed for reduct transfer:
every model of the complete reduct theory admits a formula-preserving
embedding into a same-theory expanded model. -/
def HasSameTheoryReductEmbeddingProperty
    {Symbol : Type w} {Target : Type z}
    (f : Symbol → Target) (M : MultiStructure.{u, v, z} Target) : Prop :=
  ∀ N : MultiStructure.{u, v, w} Symbol,
    MultiSameCompleteTheory (M.reduct f) N →
      Nonempty (SameTheoryReductEmbedding f M N)

end MultiStructure

namespace MultiFormula

/-- One infinite fixed-gap independence witness for a binary formula in a
many-predicate structure. -/
def HasInfiniteIPWitness {Symbol : Type w}
    (M : MultiStructure.{u, v, w} Symbol)
    (φ : MultiFormula Symbol 1 1) (low high : ℝ) : Prop :=
  ∃ rows : ℕ → M.Row,
    ∀ E F : Finset ℕ, Disjoint E F →
      ∃ parameter : M.Parameter,
        (∀ i ∈ E, φ.binaryValue M (rows i) parameter ≤ low) ∧
        (∀ i ∈ F, high ≤ φ.binaryValue M (rows i) parameter)

/-- A binary formula has IP in the complete theory of `M` when it has an
infinite fixed-gap witness in some structure with the same complete theory. -/
def HasIPInCompleteTheory {Symbol : Type w}
    (M : MultiStructure.{u, v, w} Symbol)
    (φ : MultiFormula Symbol 1 1) : Prop :=
  ∃ N : MultiStructure.{u, v, w} Symbol,
    MultiSameCompleteTheory M N ∧
      ∃ low high : ℝ, low < high ∧ HasInfiniteIPWitness N φ low high

/-- Semantic NIP in a complete many-predicate theory. -/
def IsNIPInCompleteTheory {Symbol : Type w}
    (M : MultiStructure.{u, v, w} Symbol)
    (φ : MultiFormula Symbol 1 1) : Prop :=
  ¬ HasIPInCompleteTheory M φ

/-- Pointwise equality of binary formula values preserves a fixed infinite IP
witness in both directions. -/
theorem hasInfiniteIPWitness_congr {Symbol : Type w}
    {M : MultiStructure.{u, v, w} Symbol}
    {φ ψ : MultiFormula Symbol 1 1} {low high : ℝ}
    (hvalue : ∀ x y, φ.binaryValue M x y = ψ.binaryValue M x y) :
    HasInfiniteIPWitness M φ low high ↔
      HasInfiniteIPWitness M ψ low high := by
  constructor
  · rintro ⟨rows, hrows⟩
    refine ⟨rows, ?_⟩
    intro E F hdisjoint
    obtain ⟨parameter, hlow, hhigh⟩ := hrows E F hdisjoint
    refine ⟨parameter, ?_, ?_⟩
    · intro i hi
      rw [← hvalue (rows i) parameter]
      exact hlow i hi
    · intro i hi
      rw [← hvalue (rows i) parameter]
      exact hhigh i hi
  · rintro ⟨rows, hrows⟩
    refine ⟨rows, ?_⟩
    intro E F hdisjoint
    obtain ⟨parameter, hlow, hhigh⟩ := hrows E F hdisjoint
    refine ⟨parameter, ?_, ?_⟩
    · intro i hi
      rw [hvalue (rows i) parameter]
      exact hlow i hi
    · intro i hi
      rw [hvalue (rows i) parameter]
      exact hhigh i hi

/-- An infinite IP witness for a mapped formula in an expansion is exactly an
IP witness for the original formula in the corresponding reduct. -/
theorem hasInfiniteIPWitness_map_reduct_iff
    {Symbol : Type w} {Target : Type z}
    (f : Symbol → Target) (M : MultiStructure.{u, v, z} Target)
    (φ : MultiFormula Symbol 1 1) (low high : ℝ) :
    HasInfiniteIPWitness M (φ.map f) low high ↔
      HasInfiniteIPWitness (M.reduct f) φ low high := by
  constructor
  · rintro ⟨rows, hrows⟩
    refine ⟨rows, ?_⟩
    intro E F hdisjoint
    obtain ⟨parameter, hlow, hhigh⟩ := hrows E F hdisjoint
    refine ⟨parameter, ?_, ?_⟩
    · intro i hi
      simpa only [binaryValue_map_reduct] using hlow i hi
    · intro i hi
      simpa only [binaryValue_map_reduct] using hhigh i hi
  · rintro ⟨rows, hrows⟩
    refine ⟨rows, ?_⟩
    intro E F hdisjoint
    obtain ⟨parameter, hlow, hhigh⟩ := hrows E F hdisjoint
    refine ⟨parameter, ?_, ?_⟩
    · intro i hi
      simpa only [binaryValue_map_reduct] using hlow i hi
    · intro i hi
      simpa only [binaryValue_map_reduct] using hhigh i hi

/-- A formula-preserving embedding into a same-theory expansion sends every
infinite reduct IP witness to an expansion IP witness with the same gap. -/
theorem hasInfiniteIPWitness_lift_reductEmbedding
    {Symbol : Type w} {Target : Type z}
    {f : Symbol → Target} {M : MultiStructure.{u, v, z} Target}
    {N : MultiStructure.{u, v, w} Symbol}
    (embedding : MultiStructure.SameTheoryReductEmbedding f M N)
    (φ : MultiFormula Symbol 1 1) (low high : ℝ)
    (hwitness : HasInfiniteIPWitness N φ low high) :
    HasInfiniteIPWitness embedding.expansion (φ.map f) low high := by
  obtain ⟨rows, hrows⟩ := hwitness
  refine ⟨fun i ↦ embedding.rowMap (rows i), ?_⟩
  intro E F hdisjoint
  obtain ⟨parameter, hlow, hhigh⟩ := hrows E F hdisjoint
  refine ⟨embedding.parameterMap parameter, ?_, ?_⟩
  · intro i hi
    have hvalue := congrArg (fun value : TruthValue ↦ (value : ℝ))
      (embedding.realize_reduct φ (fun _ ↦ rows i) (fun _ ↦ parameter))
    change (φ.map f).binaryValue embedding.expansion
        (embedding.rowMap (rows i)) (embedding.parameterMap parameter) =
      φ.binaryValue N (rows i) parameter at hvalue
    change (φ.map f).binaryValue embedding.expansion
      (embedding.rowMap (rows i)) (embedding.parameterMap parameter) ≤ low
    rw [hvalue]
    exact hlow i hi
  · intro i hi
    have hvalue := congrArg (fun value : TruthValue ↦ (value : ℝ))
      (embedding.realize_reduct φ (fun _ ↦ rows i) (fun _ ↦ parameter))
    change (φ.map f).binaryValue embedding.expansion
        (embedding.rowMap (rows i)) (embedding.parameterMap parameter) =
      φ.binaryValue N (rows i) parameter at hvalue
    change high ≤ (φ.map f).binaryValue embedding.expansion
      (embedding.rowMap (rows i)) (embedding.parameterMap parameter)
    rw [hvalue]
    exact hhigh i hi

/-- Formula equivalence throughout the complete theory preserves theory-level
IP in both directions. -/
theorem hasIPInCompleteTheory_congr {Symbol : Type w}
    {M : MultiStructure.{u, v, w} Symbol}
    {φ ψ : MultiFormula Symbol 1 1}
    (hequivalent : EquivalentInCompleteTheory M φ ψ) :
    HasIPInCompleteTheory M φ ↔ HasIPInCompleteTheory M ψ := by
  constructor
  · rintro ⟨N, hTheory, low, high, hgap, hwitness⟩
    refine ⟨N, hTheory, low, high, hgap, ?_⟩
    apply (hasInfiniteIPWitness_congr (M := N) (φ := φ) (ψ := ψ) ?_).mp
      hwitness
    intro x y
    exact congrArg (fun value : TruthValue ↦ (value : ℝ))
      (hequivalent N hTheory (fun _ ↦ x) (fun _ ↦ y))
  · rintro ⟨N, hTheory, low, high, hgap, hwitness⟩
    refine ⟨N, hTheory, low, high, hgap, ?_⟩
    apply (hasInfiniteIPWitness_congr (M := N) (φ := φ) (ψ := ψ) ?_).mpr
      hwitness
    intro x y
    exact congrArg (fun value : TruthValue ↦ (value : ℝ))
      (hequivalent N hTheory (fun _ ↦ x) (fun _ ↦ y))

/-- Formula equivalence throughout the complete theory preserves NIP in both
directions. -/
theorem isNIPInCompleteTheory_congr {Symbol : Type w}
    {M : MultiStructure.{u, v, w} Symbol}
    {φ ψ : MultiFormula Symbol 1 1}
    (hequivalent : EquivalentInCompleteTheory M φ ψ) :
    IsNIPInCompleteTheory M φ ↔ IsNIPInCompleteTheory M ψ :=
  not_congr (hasIPInCompleteTheory_congr hequivalent)

/-- The one-way equivalence-invariance principle in exactly the orientation
used by `ContinuousNIPSemantics.nip_of_equivalent`. -/
theorem nip_of_equivalent {Symbol : Type w}
    {M : MultiStructure.{u, v, w} Symbol}
    {φ ψ : MultiFormula Symbol 1 1}
    (hequivalent : EquivalentInCompleteTheory M φ ψ)
    (hψ : IsNIPInCompleteTheory M ψ) :
    IsNIPInCompleteTheory M φ :=
  (isNIPInCompleteTheory_congr hequivalent).mpr hψ

/-- The isolated reduct-embedding property implies the reduct-transfer
principle required by `ContinuousNIPSemantics`: NIP of a mapped formula in the
complete expansion theory gives NIP of the original formula in the complete
reduct theory. -/
theorem nip_reduct_of_expansion
    {Symbol : Type w} {Target : Type z}
    (f : Symbol → Target) (M : MultiStructure.{u, v, z} Target)
    (φ : MultiFormula Symbol 1 1)
    (hembedding : M.HasSameTheoryReductEmbeddingProperty f)
    (hNIP : IsNIPInCompleteTheory M (φ.map f)) :
    IsNIPInCompleteTheory (M.reduct f) φ := by
  intro hIP
  apply hNIP
  obtain ⟨N, hTheory, low, high, hgap, hwitness⟩ := hIP
  obtain ⟨embedding⟩ := hembedding N hTheory
  refine ⟨embedding.expansion, embedding.sameTheory, low, high, hgap, ?_⟩
  exact hasInfiniteIPWitness_lift_reductEmbedding
    embedding φ low high hwitness

end MultiFormula

end

end NormFormula.ContinuousLogic
