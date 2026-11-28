import Masullo.QRH.MeanSquare.GaussPhase
import Masullo.QRH.MeanSquare.Primary
import Masullo.QRH.MeanSquare.Residue
import Masullo.QRH.MeanSquare.Poisson

/-! # Coprime factorization of the Eisenstein Gauss sums -/

noncomputable section

open NumberField Ideal
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

private lemma generator_mem (n : Ideal 𝓔) : generator n ∈ n := by
  exact (span_singleton_le_iff_mem n).mp (span_generator n).le

private lemma embedded_generator_ne_zero {n : Ideal 𝓔} (hn : n ≠ ⊥) :
    eisEmbedding (generator n) ≠ 0 := by
  intro h
  have he := eisEmbedding_injective (h.trans (map_zero _).symm)
  exact hn (by simpa [he] using (span_generator n).symm)

/-- Coordinates for the CRT in which the representative of `(x,y)` is `c°x+b°y`. -/
private def gaussCRT {b c : Ideal 𝓔} (h : IsCoprime b c) :
    ((𝓔 ⧸ b) × (𝓔 ⧸ c)) ≃ (𝓔 ⧸ (b * c)) :=
  let u := ((isUnit_mk_iff_coprime_span b (generator c)).mpr (by rwa [span_generator])).unit
  let v := ((isUnit_mk_iff_coprime_span c (generator b)).mpr
    (by rwa [span_generator, isCoprime_comm])).unit
  ((u.mulLeft).prodCongr v.mulLeft).trans (quotientMulEquivQuotientProd b c h).symm.toEquiv

private lemma gaussCRT_mk {b c : Ideal 𝓔} (h : IsCoprime b c) (x y : 𝓔) :
    gaussCRT h (Ideal.Quotient.mk b x, Ideal.Quotient.mk c y) =
      Ideal.Quotient.mk (b * c) (generator c * x + generator b * y) := by
  apply (quotientMulEquivQuotientProd b c h).injective
  simp only [gaussCRT, Equiv.trans_apply, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
    RingEquiv.apply_symm_apply]
  apply Prod.ext <;>
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr (generator_mem _), Units.mulLeft]

/-- Under `c°x+b°y` the different character splits into its two denominator characters. -/
private lemma differentCharacter_crt {b c : Ideal 𝓔} (hb : AwayFromSix b) (hc : AwayFromSix c)
    (x y : 𝓔) : differentCharacter
      (eisEmbedding (generator c * x + generator b * y) / eisEmbedding (generator (b * c))) =
    differentCharacter (eisEmbedding x / eisEmbedding (generator b)) *
      differentCharacter (eisEmbedding y / eisEmbedding (generator c)) := by
  rw [← differentCharacter_add, generator_mul hb.coprime_three hc.coprime_three, map_add,
    map_mul, map_mul, map_mul]
  congr 1
  field_simp [embedded_generator_ne_zero hb.1, embedded_generator_ne_zero hc.1]

/-- For local multiplicative characters the CRT contributes the two cross-character values. -/
theorem gaussSum_crt {b c : Ideal 𝓔} (hb : AwayFromSix b) (hc : AwayFromSix c)
    (h : IsCoprime b c) (χ : MulChar (𝓔 ⧸ b) ℂ) (η : MulChar (𝓔 ⧸ c) ℂ) :
    (∑ᶠ t : 𝓔 ⧸ (b * c), χ (Ideal.Quotient.mk b (Quotient.out t)) *
      η (Ideal.Quotient.mk c (Quotient.out t)) * quotientDifferentCharacter (b * c) t) =
    χ (Ideal.Quotient.mk b (generator c)) * η (Ideal.Quotient.mk c (generator b)) *
      (∑ᶠ x : 𝓔 ⧸ b, χ x * quotientDifferentCharacter b x) *
      (∑ᶠ y : 𝓔 ⧸ c, η y * quotientDifferentCharacter c y) := by
  classical
  let := Ring.HasFiniteQuotients.finiteQuotient hb.1
  let := Ring.HasFiniteQuotients.finiteQuotient hc.1
  let := Ring.HasFiniteQuotients.finiteQuotient (hb.mul hc).1
  let := Fintype.ofFinite (𝓔 ⧸ b)
  let := Fintype.ofFinite (𝓔 ⧸ c)
  let := Fintype.ofFinite (𝓔 ⧸ (b * c))
  simp only [finsum_eq_sum_of_fintype]
  rw [← (gaussCRT h).sum_comp, Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [gaussCRT_mk, quotientDifferentCharacter_mk, differentCharacter_crt hb hc,
    quotientDifferentCharacter_mk, quotientDifferentCharacter_mk]
  have hout (k : Ideal 𝓔) (hk : b * c ≤ k) (t : 𝓔) :
      Ideal.Quotient.mk k (Quotient.out (Ideal.Quotient.mk (b * c) t)) = Ideal.Quotient.mk k t :=
    Ideal.Quotient.eq.mpr (hk (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out _)))
  rw [hout b Ideal.mul_le_left, hout c Ideal.mul_le_right]
  simp only [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (generator_mem _), zero_mul,
    add_zero, zero_add]
  ring

/-- The normalized Gauss sum of the `j`th power of the sextic residue symbol. -/
def normalizedGauss (n : Ideal 𝓔) (j : ℕ) : ℂ :=
  (∑ᶠ x : 𝓔 ⧸ n, sextic n (Quotient.out x) ^ j * quotientDifferentCharacter n x) /
    Real.sqrt (absNorm n)

lemma gaussCoefficient_eq (n : Ideal 𝓔) :
    gaussCoefficient n = conj (angularFactor n) * normalizedGauss n 2 := by
  unfold gaussCoefficient normalizedGauss
  rw [div_mul_eq_mul_div, mul_div_assoc]
  rfl

theorem normalizedGauss_mul {b c : Ideal 𝓔} (hb : AwayFromSix b) (hc : AwayFromSix c)
    (h : IsCoprime b c) {j : ℕ} (hj : j ≠ 0) :
    normalizedGauss (b * c) j = normalizedGauss b j * normalizedGauss c j *
      (sextic b (generator c) * sextic c (generator b)) ^ j := by
  have hcrt := gaussSum_crt hb hc h (sexticChar hb ^ j) (sexticChar hc ^ j)
  simp only [MulChar.pow_apply' _ hj, sexticChar_apply_mk] at hcrt
  have hmul (x : 𝓔) : sextic (b * c) x ^ j = sextic b x ^ j * sextic c x ^ j := by
    simp only [sextic, powerResidueSymbol_mul_right, map_mul, mul_pow]
  unfold normalizedGauss
  simp_rw [hmul, hcrt]
  rw [map_mul, Nat.cast_mul, Real.sqrt_mul (by positivity), Complex.ofReal_mul, mul_pow]
  change _ = ((∑ᶠ x, (sexticChar hb x) ^ j * quotientDifferentCharacter b x) / _ : ℂ) *
    ((∑ᶠ x, (sexticChar hc x) ^ j * quotientDifferentCharacter c x) / _) * _
  ring

lemma norm_angularFactor_eq_one {n : Ideal 𝓔} (hn : n ≠ ⊥) :
    ‖angularFactor n‖ = 1 := by
  have hc : generator n ≠ 0 := fun h => hn (by simpa [h] using (span_generator n).symm)
  have hpos := norm_pos_iff.mpr (fun he => hc (eisEmbedding_injective (he.trans (map_zero _).symm)))
  rw [angularFactor, norm_div, Complex.norm_real, Real.norm_of_nonneg hpos.le, div_self hpos.ne']

lemma angularFactor_mul {b c : Ideal 𝓔} (hb : AwayFromSix b) (hc : AwayFromSix c) :
    angularFactor (b * c) = angularFactor b * angularFactor c := by
  simp [angularFactor, generator_mul hb.coprime_three hc.coprime_three, div_mul_div_comm]

lemma sextic_sq_reciprocity (recip : DunnRadziwillReciprocity) {b c : Ideal 𝓔}
    (hb : AwayFromSix b) (hc : AwayFromSix c) :
    sextic b (generator c) ^ 2 = sextic c (generator b) ^ 2 := by
  have hr := recip.1 _ _ (eisPrimary_generator hc.coprime_three)
    (eisPrimary_generator hb.coprime_three)
  simp only [cubicSymbol, span_generator] at hr
  simpa only [sextic, ← map_pow, powerResidueSymbol_six_sq hb.2, powerResidueSymbol_six_sq hc.2]
    using congrArg eisEmbedding hr

/-- The coprime product identity in `PairedGaussIdentities` follows from cubic reciprocity. -/
theorem gaussCoefficient_mul (recip : DunnRadziwillReciprocity) {b c : Ideal 𝓔}
    (hb : AwayFromSix b) (hc : AwayFromSix c) (h : IsCoprime b c) :
    gaussCoefficient (b * c) = gaussCoefficient b * gaussCoefficient c *
      sextic c (generator b) ^ 4 := by
  rw [gaussCoefficient_eq, angularFactor_mul hb hc, map_mul,
    normalizedGauss_mul hb hc h two_ne_zero,
    mul_pow, sextic_sq_reciprocity recip hb hc, gaussCoefficient_eq, gaussCoefficient_eq]
  ring

end Masullo.QRH.MeanSquare
