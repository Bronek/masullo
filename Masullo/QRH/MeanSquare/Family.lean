import Masullo.QRH.MeanSquare.FamilyCharacter
import Masullo.QRH.MeanSquare.FamilyReciprocity

/-! # The quadratic Hecke family for the primary Eisenstein symbol -/

noncomputable section

open NumberField Ideal
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

private lemma away_of_coprime_seventyTwo {n : Ideal 𝓔} (hn : n ≠ 0)
    (hc : IsCoprime n (span {72})) : AwayFromSix n :=
  ⟨hn, hc.of_isCoprime_of_dvd_right (span_singleton_dvd_span_singleton_iff_dvd.mpr
    ⟨12, by norm_num⟩)⟩

private lemma minus_one_sq {a : Ideal 𝓔} (ha : AwayFromSix a) :
    quadraticResidue ha (-1) ^ 2 = 1 := by
  rw [← map_pow]; norm_num

/-- Equal classes have identical ramified corrections. Their product is the primitive
uncorrected character of conductor `a * b`. -/
private theorem same_class_product (quad : DeloupTuraevTheorem1) {a b : Ideal 𝓔}
    (ha : Starred a) (hb : Starred b) (h : IsCoprime a b) (he : familyClass a = familyClass b) :
    ∃ ψ : Ideal 𝓔 →*₀ ℂ, IsPrimitiveRayCharacter (a * b) ψ ∧
      ∀ d, d ≠ 0 → IsCoprime d (a * b) → IsCoprime d (quadraticConductor a) →
        IsCoprime d (quadraticConductor b) →
        ψ d = quadraticIdealCharacter ha.1 d * star (quadraticIdealCharacter hb.1 d) := by
  classical
  have hab : Starred (a * b) := ⟨ha.1.mul hb.1, squarefree_mul_iff.mpr ⟨h.isRelPrime, ha.2, hb.2⟩⟩
  have hε := sextic_neg_one_cube_eq_of_familyClass_eq quad ha hb he
  have hprod : sextic (a * b) (-1) ^ 3 = 1 := by
    rw [← quadraticResidue_apply hab.1, quadraticResidue_den_mul ha.1 hb.1]
    rw [quadraticResidue_apply, quadraticResidue_apply, hε, ← sq]
    simpa only [quadraticResidue_apply] using minus_one_sq hb.1
  refine ⟨quadraticIdealCharacter hab.1, ?_, ?_⟩
  · simpa only [quadraticConductor, ite_eq_left hprod] using quadraticIdealCharacter_primitive hab
  intro d hd _ _ hdb
  have hreal : star (quadraticIdealCharacter hb.1 d) = quadraticIdealCharacter hb.1 d := by
    rcases sq_eq_one_iff.mp (quadraticIdealCharacter_sq hb.1 hd hdb) with he | he <;> simp [he]
  rw [hreal, quadraticIdealCharacter_apply _ hd, quadraticIdealCharacter_apply _ hd,
    quadraticIdealCharacter_apply _ hd, correctedQuadratic, ite_eq_left hprod,
    quadraticResidue_den_mul ha.1 hb.1]
  by_cases hx : sextic b (-1) ^ 3 = 1
  · simp [correctedQuadratic, hx, hε]
  · rw [quadraticConductor, ite_eq_right hx] at hdb
    have hram : IsCoprime lambdaIdeal (span {generator d}) := by
      rw [span_generator]
      exact hdb.of_mul_right_right.symm
    simp only [correctedQuadratic, hε, ite_eq_right hx, MonoidHom.mul_apply,
      show ∀ x : 𝓔, lambdaSign.toMonoidHom x = lambdaSign x from fun _ => rfl]
    linear_combination -(quadraticResidue ha.1 (generator d) *
      quadraticResidue hb.1 (generator d)) *
      lambdaSign_sq hram

open Classical in
/-- The primitive ideal character attached to a good Eisenstein column `b`.
At ideals meeting six or at the zero ideal we use the character at the unit ideal. -/
def eisensteinQuadraticCharacter (b : Ideal 𝓔) : Ideal 𝓔 →*₀ ℂ :=
  if hb : AwayFromSix b then quadraticIdealCharacter hb else
    quadraticIdealCharacter (show AwayFromSix 1 from ⟨one_ne_zero, isCoprime_one_left⟩)

lemma eisensteinQuadraticCharacter_of_good {b : Ideal 𝓔} (hb : AwayFromSix b) :
    eisensteinQuadraticCharacter b = quadraticIdealCharacter hb := dite_eq_left hb

/-- The Eisenstein characters satisfy Definition 1 of Goldmakher–Louvel for `c = (72)`. -/
theorem eisensteinQuadraticHeckeFamily (quad : DeloupTuraevTheorem1) :
    IsQuadraticHeckeFamily (span {72}) eisensteinQuadraticCharacter quadraticConductor := by
  constructor
  · intro a hsf hc
    have ha : Starred a := ⟨away_of_coprime_seventyTwo hsf.ne_zero hc, hsf⟩
    rw [eisensteinQuadraticCharacter_of_good ha.1]
    exact ⟨quadraticIdealCharacter_primitive ha, fun _ => quadraticIdealCharacter_sq ha.1⟩
  · refine ⟨QuadraticFamilyClass, inferInstance, inferInstance, familyClass, familySign,
      familyClass_one, ?_, familySign_sq, ?_⟩
    · intro a b ha hb hca hcb
      exact familyClass_mul (away_of_coprime_seventyTwo ha hca) (away_of_coprime_seventyTwo hb hcb)
    · intro a b hsa hca hsb hcb hab
      have ha : Starred a := ⟨away_of_coprime_seventyTwo hsa.ne_zero hca, hsa⟩
      have hb : Starred b := ⟨away_of_coprime_seventyTwo hsb.ne_zero hcb, hsb⟩
      rw [eisensteinQuadraticCharacter_of_good ha.1, eisensteinQuadraticCharacter_of_good hb.1,
        quadraticIdealCharacter_good ha.1 hb.1, quadraticIdealCharacter_good hb.1 ha.1]
      exact ⟨primaryQuadraticSymbol_reciprocity quad ha hb hab, same_class_product quad ha hb hab⟩

/-- The characters agree with the primary residue symbol, including zeros at common factors. -/
lemma eisensteinQuadraticCharacter_eq_symbol {a b : Ideal 𝓔}
    (ha : AwayFromSix a) (hb : AwayFromSix b) :
    eisensteinQuadraticCharacter b a = primaryQuadraticSymbol a b := by
  rw [eisensteinQuadraticCharacter_of_good hb, quadraticIdealCharacter_good hb ha]

/-- Index multiplicativity `χ_{gb}(a) = χ_g(a) χ_b(a)` on ideals prime to six, used in
Goldmakher–Louvel, §4, Lemma 4.6, and §5.1. -/
theorem eisensteinQuadraticCharacter_mul {g b a : Ideal 𝓔} (hg : AwayFromSix g)
    (hb : AwayFromSix b) (ha : AwayFromSix a) :
    eisensteinQuadraticCharacter (g * b) a =
      eisensteinQuadraticCharacter g a * eisensteinQuadraticCharacter b a := by
  rw [eisensteinQuadraticCharacter_of_good (hg.mul hb), eisensteinQuadraticCharacter_of_good hg,
    eisensteinQuadraticCharacter_of_good hb, quadraticIdealCharacter_mul hg hb ha]

/-- On ideals prime to six, `χ_b(a) = 0` exactly when `a` and `b` share a prime. -/
theorem eisensteinQuadraticCharacter_eq_zero_iff {b a : Ideal 𝓔} (hb : AwayFromSix b)
    (ha : AwayFromSix a) : eisensteinQuadraticCharacter b a = 0 ↔ ¬ IsCoprime a b := by
  rw [eisensteinQuadraticCharacter_of_good hb, quadraticIdealCharacter_eq_zero_iff hb ha]

/-- Distinct squarefree indices give a product `χ_b χ̄_c` with value `-1` on an ideal coprime
to six and to both indices, as required in Goldmakher–Louvel, §4, (E₂). -/
theorem eisensteinQuadraticCharacter_product_nonprincipal {b c : Ideal 𝓔}
    (hb : Starred b) (hc : Starred c) (hne : b ≠ c) :
    ∃ a : Ideal 𝓔, AwayFromSix a ∧ IsCoprime a b ∧ IsCoprime a c ∧
      eisensteinQuadraticCharacter b a * star (eisensteinQuadraticCharacter c a) = -1 := by
  rw [eisensteinQuadraticCharacter_of_good hb.1, eisensteinQuadraticCharacter_of_good hc.1]
  exact quadraticIdealCharacter_product_nonprincipal hb hc hne

theorem eisensteinFamilyRealizes (quad : DeloupTuraevTheorem1) :
    EisensteinFamilyRealizes primaryQuadraticSymbol :=
  ⟨eisensteinQuadraticCharacter, quadraticConductor, eisensteinQuadraticHeckeFamily quad,
    fun _ _ hsa hca hsb hcb => eisensteinQuadraticCharacter_eq_symbol
      (away_of_coprime_seventyTwo hsa.ne_zero hca) (away_of_coprime_seventyTwo hsb.ne_zero hcb)⟩

/-- L. Goldmakher and B. Louvel, *A quadratic large sieve inequality over number fields*,
Math. Proc. Cambridge Philos. Soc. 154 (2013), Theorem 1.1, pp. 194–195,
specialized to the family `eisensteinQuadraticCharacter` over ℚ(ω) with `c = (72)`.
The starred sums run over squarefree ideals prime to `c`, with column `b` evaluated at row `a`.
The printed proof uses four properties of the family beyond Definition 1, all of which
hold here:
* the group `G` of §4, Lemma 4.5, is the fixed `QuadraticFamilyClass`, the units modulo 4;
* the conductor has norm at most `3 N(b)` (`absNorm_quadraticConductor_le`) and lies between
  `b` and `b` times the prime above three (`dvd_quadraticConductor`,
  `quadraticConductor_dvd`), so `χ_b(a) = 0` exactly when `a` and `b` share a prime
  (`eisensteinQuadraticCharacter_eq_zero_iff`);
* products at distinct indices are nonprincipal
  (`eisensteinQuadraticCharacter_product_nonprincipal`);
* the characters are multiplicative in the index (`eisensteinQuadraticCharacter_mul`).
The premise records that the family satisfies Definition 1, the hypothesis of Theorem 1.1;
`eisensteinQuadraticHeckeFamily` proves it from `DeloupTuraevTheorem1`.
<https://arxiv.org/pdf/1112.1642v2#page=2> -/
def EisensteinGoldmakherLouvel : Prop :=
  IsQuadraticHeckeFamily (span {72}) eisensteinQuadraticCharacter quadraticConductor →
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
  ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    SieveBound (sieveIdeals (span {72}) M) (sieveIdeals (span {72}) N)
      (fun a b => eisensteinQuadraticCharacter b a) (C * (M * N) ^ ε * (M + N))

/-- Restrict Theorem 1.1 to the manuscript's dyadic columns and identify its entries. -/
theorem quadraticSieve_of_goldmakherLouvel (hGL : EisensteinGoldmakherLouvel)
    (quad : DeloupTuraevTheorem1) : QuadraticSieve primaryQuadraticSymbol := by
  classical
  intro ε hε
  obtain ⟨C, hC, hGL⟩ := hGL (eisensteinQuadraticHeckeFamily quad) ε hε
  refine ⟨2 * (2 : ℝ) ^ ε * C, by positivity, ?_⟩
  intro M N hM hN rows cols hr hc
  have hr' := hr.trans sieveIdeals_six_subset_seventyTwo
  have hc' := (hc.trans (Finset.filter_subset _ _)).trans sieveIdeals_six_subset_seventyTwo
  have h := (hGL M (2 * N) hM (by linarith)).restrict hr' hc'
  intro z
  have heq (a) (ha : a ∈ rows) (b) (hb : b ∈ cols) :
      eisensteinQuadraticCharacter b a = primaryQuadraticSymbol a b := by
    have har := hr' ha
    have hbc := hc' hb
    simp only [sieveIdeals, Finset.mem_filter] at har hbc
    exact eisensteinQuadraticCharacter_eq_symbol (away_of_coprime_seventyTwo
      har.2.1.ne_zero har.2.2)
      (away_of_coprime_seventyTwo hbc.2.1.ne_zero hbc.2.2)
  have hrow (a) (ha : a ∈ rows) : ∑ b ∈ cols, z b * eisensteinQuadraticCharacter b a =
      ∑ b ∈ cols, z b * primaryQuadraticSymbol a b :=
    Finset.sum_congr rfl fun b hb => by rw [heq a ha b hb]
  have hz := h z
  dsimp only at hz
  rw [Finset.sum_congr rfl (fun a ha => congrArg (fun t : ℂ => ‖t‖ ^ 2) (hrow a ha))] at hz
  refine hz.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have hMN : 0 ≤ M * N := by positivity
  rw [show M * (2 * N) = (M * N) * 2 by ring, Real.mul_rpow hMN (by norm_num)]
  have hpos : 0 ≤ C * ((M * N) ^ ε * 2 ^ ε) := by positivity
  calc
    _ ≤ C * ((M * N) ^ ε * 2 ^ ε) * (2 * (M + N)) :=
      mul_le_mul_of_nonneg_left (by linarith) hpos
    _ = _ := by ring

end Masullo.QRH.MeanSquare
