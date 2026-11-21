import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import NormFormula.ModelTheory.LocalNIP

/-!
# Bounded local NIP for Hilbert norm translations

This file gives a finite-pattern proof of the local consequence of Hilbert
stability needed by the paper.  The key Hilbertian input is a deterministic
sign choice whose signed sum has square norm no larger than the sum of the
individual square norms.
-/

namespace NormFormula

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Signs can be chosen so that a finite signed sum has square norm at most
the sum of the individual square norms. -/
theorem exists_sign_sum_norm_sq_le {ι : Type*} (s : Finset ι) (v : ι → E) :
    ∃ ε : ι → ℝ,
      (∀ i ∈ s, ε i = 1 ∨ ε i = -1) ∧
      ‖∑ i ∈ s, ε i • v i‖ ^ 2 ≤ ∑ i ∈ s, ‖v i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨fun _ ↦ 1, ?_, by simp⟩
      simp
  | @insert a s ha ih =>
      obtain ⟨ε, hε, hbound⟩ := ih
      let w : E := ∑ i ∈ s, ε i • v i
      let sign : ℝ := if 0 ≤ ⟪v a, w⟫_ℝ then -1 else 1
      let ε' : ι → ℝ := Function.update ε a sign
      have hsign : sign = 1 ∨ sign = -1 := by
        dsimp [sign]
        split_ifs <;> simp
      have hcross : ⟪sign • v a, w⟫_ℝ ≤ 0 := by
        rw [real_inner_smul_left]
        dsimp [sign]
        split_ifs with h <;> simp <;> linarith
      have hsum : ∑ i ∈ insert a s, ε' i • v i = sign • v a + w := by
        rw [Finset.sum_insert ha]
        rw [show ε' a = sign by simp [ε']]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [show ε' i = ε i by
          apply Function.update_of_ne
          exact fun hia ↦ ha (hia ▸ hi)]
      refine ⟨ε', ?_, ?_⟩
      · intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · simpa [ε'] using hsign
        · have hia : i ≠ a := fun hia ↦ ha (hia ▸ hi)
          simpa [ε', Function.update_of_ne hia] using hε i hi
      · rw [hsum, Finset.sum_insert ha, norm_add_sq_real]
        have hsignNorm : ‖sign • v a‖ ^ 2 = ‖v a‖ ^ 2 := by
          rcases hsign with h | h
          · rw [h]
            simp
          · rw [h]
            simp
        rw [hsignNorm]
        dsimp [w] at hbound ⊢
        linarith

/-- A Hilbert-space linear class with row square norms at most `A`, parameter
square norms at most `B`, and signed margin `δ` can shatter only a family
whose cardinality satisfies `n δ² ≤ A B`. -/
theorem card_mul_margin_sq_le_of_inner_sign_shattered
    {n : ℕ} (v : Fin n → E) {A B δ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hv : ∀ i, ‖v i‖ ^ 2 ≤ A)
    (hshatter : ∀ ε : Fin n → ℝ,
      (∀ i, ε i = 1 ∨ ε i = -1) →
      ∃ w : E, ‖w‖ ^ 2 ≤ B ∧ ∀ i, δ ≤ ε i * ⟪v i, w⟫_ℝ) :
    (n : ℝ) * δ ^ 2 ≤ A * B := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [mul_nonneg hA hB]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  obtain ⟨ε, hε, hsignSum⟩ :=
    exists_sign_sum_norm_sq_le (Finset.univ : Finset (Fin n)) v
  obtain ⟨w, hw, hmargin⟩ := hshatter ε (fun i ↦ hε i (Finset.mem_univ i))
  let z : E := ∑ i, ε i • v i
  have hzsq : ‖z‖ ^ 2 ≤ (n : ℝ) * A := by
    calc
      ‖z‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2 := by simpa [z] using hsignSum
      _ ≤ ∑ _i : Fin n, A := Finset.sum_le_sum fun i _ ↦ hv i
      _ = (n : ℝ) * A := by simp
  have hsumMargin : (n : ℝ) * δ ≤ ⟪z, w⟫_ℝ := by
    calc
      (n : ℝ) * δ = ∑ _i : Fin n, δ := by simp
      _ ≤ ∑ i, ε i * ⟪v i, w⟫_ℝ :=
        Finset.sum_le_sum fun i _ ↦ hmargin i
      _ = ⟪z, w⟫_ℝ := by
        simp [z, sum_inner, real_inner_smul_left]
  have hinner : (n : ℝ) * δ ≤ ‖z‖ * ‖w‖ :=
    hsumMargin.trans (real_inner_le_norm z w)
  have hleftNonneg : 0 ≤ (n : ℝ) * δ := mul_nonneg hnpos.le hδ
  have hrightNonneg : 0 ≤ ‖z‖ * ‖w‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsquare : ((n : ℝ) * δ) ^ 2 ≤ ‖z‖ ^ 2 * ‖w‖ ^ 2 := by
    rw [← mul_pow]
    exact (sq_le_sq₀ hleftNonneg hrightNonneg).2 hinner
  have hproduct : ‖z‖ ^ 2 * ‖w‖ ^ 2 ≤ ((n : ℝ) * A) * B :=
    mul_le_mul hzsq hw (sq_nonneg _) (mul_nonneg hnpos.le hA)
  nlinarith

/-- Hilbert feature space used to linearize a squared norm threshold. -/
abbrev HilbertNormFeature (E : Type*) :=
  WithLp 2 (E × WithLp 2 (ℝ × ℝ))

/-- Row feature `(2x, ‖x‖², 1)`. -/
noncomputable def hilbertNormRowFeature (x : E) : HilbertNormFeature E :=
  WithLp.toLp 2 ((2 : ℝ) • x, WithLp.toLp 2 (‖x‖ ^ 2, 1))

/-- Parameter feature `(y, 1, ‖y‖²-t)` for squared threshold `t`. -/
noncomputable def hilbertNormParameterFeature (y : E) (t : ℝ) :
    HilbertNormFeature E :=
  WithLp.toLp 2 (y, WithLp.toLp 2 (1, ‖y‖ ^ 2 - t))

private theorem real_inner_real_eq_mul (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  conv_lhs =>
    rw [show a = a • (1 : ℝ) by simp, show b = b • (1 : ℝ) by simp]
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  norm_num

/-- The feature inner product is the squared translate norm minus the chosen
threshold. -/
theorem hilbertNormRowFeature_inner_parameterFeature (x y : E) (t : ℝ) :
    ⟪hilbertNormRowFeature x, hilbertNormParameterFeature y t⟫_ℝ =
      ‖x + y‖ ^ 2 - t := by
  unfold hilbertNormRowFeature hilbertNormParameterFeature
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply, norm_add_sq_real]
  rw [real_inner_smul_left, real_inner_real_eq_mul, real_inner_real_eq_mul]
  ring

/-- Exact square norm of a row feature. -/
theorem hilbertNormRowFeature_norm_sq (x : E) :
    ‖hilbertNormRowFeature x‖ ^ 2 =
      4 * ‖x‖ ^ 2 + ‖x‖ ^ 4 + 1 := by
  unfold hilbertNormRowFeature
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  have htwo : ‖(2 : ℝ) • x‖ = 2 * ‖x‖ := by
    rw [norm_smul]
    norm_num
  change ‖(2 : ℝ) • x‖ ^ 2 +
      (‖(‖x‖ ^ 2 : ℝ)‖ ^ 2 + ‖(1 : ℝ)‖ ^ 2) = _
  rw [htwo]
  simp only [Real.norm_of_nonneg (sq_nonneg ‖x‖), norm_one]
  ring

omit [InnerProductSpace ℝ E] in
/-- Exact square norm of a parameter feature. -/
theorem hilbertNormParameterFeature_norm_sq (y : E) (t : ℝ) :
    ‖hilbertNormParameterFeature y t‖ ^ 2 =
      ‖y‖ ^ 2 + 1 + (‖y‖ ^ 2 - t) ^ 2 := by
  unfold hilbertNormParameterFeature
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  change ‖y‖ ^ 2 +
      (‖(1 : ℝ)‖ ^ 2 + ‖(‖y‖ ^ 2 - t : ℝ)‖ ^ 2) = _
  rw [norm_one, Real.norm_eq_abs, sq_abs]
  ring

/-- Uniform square-norm bound for row features from a row-ball bound. -/
theorem hilbertNormRowFeature_norm_sq_le (x : E) {R : ℝ} (hx : ‖x‖ ≤ R) :
    ‖hilbertNormRowFeature x‖ ^ 2 ≤ 4 * R ^ 2 + R ^ 4 + 1 := by
  have hR : 0 ≤ R := (norm_nonneg x).trans hx
  have hsq : ‖x‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg x) hR).2 hx
  have hfourth : ‖x‖ ^ 4 ≤ R ^ 4 := by
    have h := (sq_le_sq₀ (sq_nonneg ‖x‖) (sq_nonneg R)).2 hsq
    nlinarith
  rw [hilbertNormRowFeature_norm_sq]
  linarith

omit [InnerProductSpace ℝ E] in
/-- Uniform square-norm bound for parameter features from a parameter-ball
bound. -/
theorem hilbertNormParameterFeature_norm_sq_le
    (y : E) (t : ℝ) {R : ℝ} (hy : ‖y‖ ≤ R) :
    ‖hilbertNormParameterFeature y t‖ ^ 2 ≤
      R ^ 2 + 1 + 2 * R ^ 4 + 2 * t ^ 2 := by
  have hR : 0 ≤ R := (norm_nonneg y).trans hy
  have hsq : ‖y‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg y) hR).2 hy
  have hfourth : ‖y‖ ^ 4 ≤ R ^ 4 := by
    have h := (sq_le_sq₀ (sq_nonneg ‖y‖) (sq_nonneg R)).2 hsq
    nlinarith
  rw [hilbertNormParameterFeature_norm_sq]
  nlinarith [sq_nonneg (‖y‖ ^ 2 + t)]

/-- Translation followed by the norm on a real inner-product space. -/
def hilbertNormTranslate (x y : E) : ℝ := ‖x + y‖

/-- Quantitative finite-pattern bound for Hilbert norm translations.  The
square-norm thresholds are linearized in `HilbertNormFeature E`, and the sign
choice estimate supplies the displayed dimension inequality. -/
theorem card_mul_sqGap_sq_le_of_hilbertNorm_IPPattern
    {n : ℕ} (rows : Fin n → E) {R_x R_y low high : ℝ}
    (hn : 0 < n) (hgap : low < high)
    (hrows : ∀ i, ‖rows i‖ ≤ R_x)
    (hip : IsIPPattern
      (boundedBinaryValue hilbertNormTranslate rows R_y) low high) :
    (n : ℝ) * ((high ^ 2 - low ^ 2) / 2) ^ 2 ≤
      (4 * R_x ^ 2 + R_x ^ 4 + 1) *
        (R_y ^ 2 + 1 + 2 * R_y ^ 4 +
          2 * ((high ^ 2 + low ^ 2) / 2) ^ 2) := by
  classical
  let i₀ : Fin n := ⟨0, hn⟩
  obtain ⟨y₀, _hin₀, hout₀⟩ := hip ∅
  have hlowBound : ‖rows i₀ + y₀.1‖ ≤ low := by
    simpa [boundedBinaryValue, hilbertNormTranslate] using hout₀ i₀ (by simp)
  have hlow : 0 ≤ low := (norm_nonneg _).trans hlowBound
  have hhigh : 0 < high := hlow.trans_lt hgap
  have hRx : 0 ≤ R_x := (norm_nonneg (rows i₀)).trans (hrows i₀)
  have hRy : 0 ≤ R_y := (norm_nonneg y₀.1).trans y₀.2
  let δ := (high ^ 2 - low ^ 2) / 2
  let t := (high ^ 2 + low ^ 2) / 2
  let A := 4 * R_x ^ 2 + R_x ^ 4 + 1
  let B := R_y ^ 2 + 1 + 2 * R_y ^ 4 + 2 * t ^ 2
  have hδ : 0 < δ := by
    dsimp [δ]
    have hsquare : low ^ 2 < high ^ 2 :=
      (sq_lt_sq₀ hlow hhigh.le).2 hgap
    linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfeatureRows : ∀ i, ‖hilbertNormRowFeature (rows i)‖ ^ 2 ≤ A := by
    intro i
    simpa [A] using hilbertNormRowFeature_norm_sq_le (rows i) (hrows i)
  have hlinearShatter : ∀ ε : Fin n → ℝ,
      (∀ i, ε i = 1 ∨ ε i = -1) →
      ∃ w : HilbertNormFeature E, ‖w‖ ^ 2 ≤ B ∧
        ∀ i, δ ≤ ε i * ⟪hilbertNormRowFeature (rows i), w⟫_ℝ := by
    intro ε hε
    let S : Finset (Fin n) := Finset.univ.filter fun i ↦ ε i = 1
    obtain ⟨y, hin, hout⟩ := hip S
    refine ⟨hilbertNormParameterFeature y.1 t, ?_, ?_⟩
    · simpa [B] using hilbertNormParameterFeature_norm_sq_le y.1 t y.2
    · intro i
      rw [hilbertNormRowFeature_inner_parameterFeature]
      rcases hε i with hi | hi
      · have hiS : i ∈ S := by simp [S, hi]
        have hvalue := hin i hiS
        have hsquare : high ^ 2 ≤ ‖rows i + y.1‖ ^ 2 :=
          (sq_le_sq₀ hhigh.le (norm_nonneg _)).2
            (by simpa [boundedBinaryValue, hilbertNormTranslate] using hvalue)
        rw [hi]
        dsimp [δ, t]
        norm_num
        linarith
      · have hiS : i ∉ S := by norm_num [S, hi]
        have hvalue := hout i hiS
        have hsquare : ‖rows i + y.1‖ ^ 2 ≤ low ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) hlow).2
            (by simpa [boundedBinaryValue, hilbertNormTranslate] using hvalue)
        rw [hi]
        dsimp [δ, t]
        norm_num
        linarith
  have hdimension := card_mul_margin_sq_le_of_inner_sign_shattered
    (fun i ↦ hilbertNormRowFeature (rows i)) hA hB hδ.le
    hfeatureRows hlinearShatter
  simpa [δ, t, A, B] using hdimension

/-- Hilbert norm translations have bounded local NIP, uniformly over the
dimension of the real inner-product space. -/
theorem hilbertNormTranslate_isBoundedLocalNIP :
    IsBoundedLocalNIP (hilbertNormTranslate (E := E)) := by
  intro R_x R_y low high hgap
  let δ := (high ^ 2 - low ^ 2) / 2
  let t := (high ^ 2 + low ^ 2) / 2
  let A := 4 * R_x ^ 2 + R_x ^ 4 + 1
  let B := R_y ^ 2 + 1 + 2 * R_y ^ 4 + 2 * t ^ 2
  let N := ⌊A * B / δ ^ 2⌋₊ + 1
  refine ⟨N, ?_⟩
  intro n rows hrows hip
  by_cases hnzero : n = 0
  · subst n
    dsimp [N]
    omega
  have hn : 0 < n := Nat.pos_of_ne_zero hnzero
  let i₀ : Fin n := ⟨0, hn⟩
  obtain ⟨y₀, _hin₀, hout₀⟩ := hip ∅
  have hlowBound : ‖rows i₀ + y₀.1‖ ≤ low := by
    simpa [boundedBinaryValue, hilbertNormTranslate] using hout₀ i₀ (by simp)
  have hlow : 0 ≤ low := (norm_nonneg _).trans hlowBound
  have hhigh : 0 < high := hlow.trans_lt hgap
  have hδ : 0 < δ := by
    dsimp [δ]
    have hsquare : low ^ 2 < high ^ 2 :=
      (sq_lt_sq₀ hlow hhigh.le).2 hgap
    linarith
  have hdimension := card_mul_sqGap_sq_le_of_hilbertNorm_IPPattern
    rows hn hgap hrows hip
  have hdimension' : (n : ℝ) * δ ^ 2 ≤ A * B := by
    simpa [δ, t, A, B] using hdimension
  have hn_le_ratio : (n : ℝ) ≤ A * B / δ ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hδ)).2 hdimension'
  have hratio_lt_N : A * B / δ ^ 2 < (N : ℝ) := by
    simpa [N] using (Nat.lt_floor_add_one (A * B / δ ^ 2))
  have hn_lt_N : (n : ℝ) < N := hn_le_ratio.trans_lt hratio_lt_N
  exact_mod_cast hn_lt_N

end NormFormula
