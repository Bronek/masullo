import Masullo.QRH.MeanSquare.GaussProduct

/-! # Changing the additive character in the cubic Gauss sum -/

noncomputable section

open NumberField Ideal Complex
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

lemma coprime_span_lambda {n : Ideal 𝓔} (hn : AwayFromSix n) :
    IsCoprime n (span {eisLambda}) := by
  refine hn.coprime_three.of_isCoprime_of_dvd_right
    (span_singleton_dvd_span_singleton_iff_dvd.mpr ⟨-eisLambda, ?_⟩)
  rw [mul_neg, ← sq, eisLambda_sq, neg_neg]

private lemma pattersonGauss_eq_finsum (c : 𝓔) :
    pattersonGauss 1 c = ∑ᶠ x : 𝓔 ⧸ span {c}, eisEmbedding (cubicSymbol (Quotient.out x) c) *
      traceCharacter (eisEmbedding (Quotient.out x) / eisEmbedding c) := by
  classical
  by_cases hc : c = 1
  · subst c
    let : Subsingleton (𝓔 ⧸ span {(1 : 𝓔)}) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
    let := Fintype.ofFinite (𝓔 ⧸ span {(1 : 𝓔)})
    simp [finsum_eq_sum_of_fintype]
  · simp [pattersonGauss, hc, traceCharacter]

set_option maxHeartbeats 800000 in
private lemma pattersonGauss_eq_mulShift {n : Ideal 𝓔} (hn : AwayFromSix n) [Fintype (𝓔 ⧸ n)] :
    pattersonGauss 1 (generator n) = gaussSum (sexticChar hn ^ 2)
      ((quotientDifferentCharacter n).mulShift (Ideal.Quotient.mk n eisLambda)) := by
  obtain ⟨c, hc, hp⟩ := exists_primary_generator hn.coprime_three
  subst n
  have hg := generator_eq_of_eisPrimary rfl hp
  rw [hg, pattersonGauss_eq_finsum, finsum_eq_sum_of_fintype, gaussSum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h₁ : (sexticChar hn ^ 2) x = eisEmbedding (cubicSymbol (Quotient.out x) c) := by
    rw [MulChar.pow_apply' _ two_ne_zero]
    change eisEmbedding (powerResidueSymbol 6 (Quotient.out x) (span {c})) ^ 2 = _
    rw [← map_pow, powerResidueSymbol_six_sq hn.2]
    rfl
  rw [h₁, AddChar.mulShift_apply]
  congr 1
  have he : Ideal.Quotient.mk (span {c}) eisLambda * x =
      Ideal.Quotient.mk _ (eisLambda * Quotient.out x) := by rw [map_mul, Ideal.Quotient.mk_out]
  rw [he, quotientDifferentCharacter_mk, hg, map_mul, mul_div_assoc, differentCharacter_lambda_mul]

set_option maxHeartbeats 800000 in
/-- Passing from the trace character to the different character twists the cubic Gauss sum
by the cubic symbol of the different. -/
theorem gaussCoefficient_eq_pattersonGauss {n : Ideal 𝓔} (hn : AwayFromSix n) :
    gaussCoefficient n = conj (angularFactor n) * sextic n eisLambda ^ 2 *
      (pattersonGauss 1 (generator n) / ‖eisEmbedding (generator n)‖) := by
  classical
  let := Ring.HasFiniteQuotients.finiteQuotient hn.1
  let := Fintype.ofFinite (𝓔 ⧸ n)
  obtain ⟨u, hu⟩ := (isUnit_mk_iff_coprime_span n eisLambda).mpr (coprime_span_lambda hn)
  have h := gaussSum_mulShift (sexticChar hn ^ 2) (quotientDifferentCharacter n) u
  rw [hu, ← pattersonGauss_eq_mulShift hn, MulChar.pow_apply' _ two_ne_zero,
    sexticChar_apply_mk] at h
  rw [gaussCoefficient, finsum_eq_sum_of_fintype, norm_eisEmbedding_generator]
  change conj (angularFactor n) / _ * ∑ x : 𝓔 ⧸ n, sexticChar hn x ^ 2 *
    quotientDifferentCharacter n x = _
  simp_rw [← MulChar.pow_apply' _ (by decide : 2 ≠ 0)]
  rw [← gaussSum]
  rw [← h]
  ring

/-- The normalized cubic Gauss sum for the different character cubes to the Möbius sign
times the angular factor. -/
theorem gaussCoefficient_mul_angularFactor_cube (h : DunnRadziwillGaussCube) {n : Ideal 𝓔}
    (hn : AwayFromSix n) :
    (gaussCoefficient n * angularFactor n) ^ 3 = (idealMoebius n : ℂ) * angularFactor n := by
  have hα : (angularFactor n) * conj (angularFactor n) = 1 := by
    rw [Complex.mul_conj', norm_angularFactor_eq_one hn.1]; norm_num
  have hphase : sextic n eisLambda ^ 6 = 1 := by
    simp only [sextic, ← map_pow, powerResidueSymbol_six_pow_six hn.1 hn.2,
      ite_eq_left (coprime_span_lambda hn), map_one]
  have hc := h (generator n) (eisPrimary_generator hn.coprime_three)
  rw [span_generator] at hc
  rw [gaussCoefficient_eq_pattersonGauss hn]
  calc
    _ = (angularFactor n * conj (angularFactor n)) ^ 3 * sextic n eisLambda ^ 6 *
          (pattersonGauss 1 (generator n) / (‖eisEmbedding (generator n)‖ : ℂ)) ^ 3 := by ring
    _ = _ := by rw [hα, hphase, hc, one_pow, one_mul, one_mul, angularFactor]; ring

end Masullo.QRH.MeanSquare
