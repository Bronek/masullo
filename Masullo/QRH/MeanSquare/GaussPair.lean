import Masullo.QRH.MeanSquare.GaussSquare
import Masullo.QRH.MeanSquare.GaussCube

/-! # Ray corrections for the paired Gauss sums -/

noncomputable section

open NumberField Ideal
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)
local notation "Ray" => 𝓔 ⧸ span {(72 : 𝓔)}

private def ray (n : Ideal 𝓔) : Ray := Ideal.Quotient.mk _ (generator n)

private def fourCorrection (r : Ray) : ℂ :=
  eisEmbedding (cubicSymbol (Quotient.out r) (-2))

private lemma fourCorrection_ray (recip : DunnRadziwillReciprocity) {n : Ideal 𝓔}
    (hn : AwayFromSix n) : fourCorrection (ray n) = sextic n 4 := by
  have hle : span {(72 : 𝓔)} ≤ span {-2} := by
    rw [span_singleton_le_span_singleton]
    exact ⟨-36, by norm_num⟩
  have hc := Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (ray n))
  have hr := cubicSymbol_neg_two recip (eisPrimary_generator hn.coprime_three)
  rw [fourCorrection, cubicSymbol, powerResidueSymbol_congr (Ideal.Quotient.eq.mpr (hle hc))]
  change eisEmbedding (cubicSymbol (generator n) (-2)) = _
  rw [← hr, cubicSymbol, span_generator, ← powerResidueSymbol_six_sq hn.2]
  rw [show (4 : 𝓔) = (-2) * (-2) by norm_num, sextic, powerResidueSymbol_six_mul hn.2, sq]

private lemma sextic_six {n : Ideal 𝓔} (hn : AwayFromSix n) {a : 𝓔}
    (ha : IsCoprime n (span {a})) : sextic n a ^ 6 = 1 := by
  simp only [sextic, ← map_pow, powerResidueSymbol_six_pow_six hn.1 hn.2, ite_eq_left ha, map_one]

private lemma cross_cubic (recip : DunnRadziwillReciprocity) {b c : Ideal 𝓔}
    (hb : AwayFromSix b) (hc : AwayFromSix c) (h : IsCoprime b c) :
    conj (sextic b (generator c)) * sextic c (generator b) =
      (sextic b (generator c) * sextic c (generator b)) ^ 3 := by
  let x := sextic b (generator c)
  let y := sextic c (generator b)
  have hn : ‖x‖ = 1 := norm_sextic_of_coprime hb (by rwa [span_generator])
  have hx : x ^ 6 = 1 := sextic_six hb (by rwa [span_generator])
  have hxy : x ^ 2 = y ^ 2 := sextic_sq_reciprocity recip hb hc
  have hu : x * conj x = 1 := by rw [Complex.mul_conj', hn]; norm_num
  change conj x * y = (x * y)^3
  calc
    _ = conj x * y * x ^ 6 := by rw [hx, mul_one]
    _ = (x * conj x) * x ^ 3 * x ^ 2 * y := by ring
    _ = _ := by rw [hu, hxy]; ring

/-- Reversing the additive character changes a Gauss sum by the value at minus one. -/
private lemma gaussSum_star_left {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (ψ : AddChar R ℂ) :
    gaussSum (star χ) ψ = conj (χ (-1)) * conj (gaussSum χ ψ) := by
  have h := star_gaussSum_eq χ ψ⁻¹
  rw [inv_inv, gaussSum_inv_right] at h
  simpa only [MulChar.star_eq_inv, ← map_mul, Complex.star_def] using h.symm

private lemma quadraticChar_real {n : Ideal 𝓔} (hn : AwayFromSix n) :
    star (sexticChar hn ^ 3) = sexticChar hn ^ 3 := by
  classical
  ext u
  have hu : IsCoprime n (span {Quotient.out (u : 𝓔 ⧸ n)}) :=
    (isUnit_mk_iff_coprime_span _ _).mp (by rw [Ideal.Quotient.mk_out]; exact u.isUnit)
  let z := sextic n (Quotient.out (u : 𝓔 ⧸ n))
  have hz : z ^ 6 = 1 := sextic_six hn hu
  have h3 : z ^ 3 = 1 ∨ z ^ 3 = -1 := sq_eq_one_iff.mp (by rw [← pow_mul]; exact hz)
  simp only [MulChar.star_apply, MulChar.pow_apply' _ (by decide : 3 ≠ 0)]
  change star (z ^ 3) = z ^ 3
  rcases h3 with he | he <;> simp [he]

private lemma neg_one_sextic_sq {n : Ideal 𝓔} (hn : AwayFromSix n) :
    sextic n (-1) ^ 2 = 1 := by
  have he := map_mul (sexticChar hn) (Ideal.Quotient.mk n (-1)) (Ideal.Quotient.mk n (-1))
  simpa only [← map_mul, neg_one_mul, neg_neg, map_one, sexticChar_apply_mk, sq] using he.symm

lemma quadraticGauss_conj {n : Ideal 𝓔} (hn : AwayFromSix n) :
    conj (sextic n (-1)) * conj (normalizedGauss n 3) = normalizedGauss n 3 := by
  classical
  let := Ring.HasFiniteQuotients.finiteQuotient hn.1
  let := Fintype.ofFinite (𝓔 ⧸ n)
  have hg := gaussSum_star_left (sexticChar hn ^ 3) (quotientDifferentCharacter n)
  rw [quadraticChar_real hn, MulChar.pow_apply' _ (by decide : 3 ≠ 0),
    show sexticChar hn (-1) = sextic n (-1) by simpa using sexticChar_apply_mk hn (-1)] at hg
  rw [pow_succ (sextic n (-1)) 2, neg_one_sextic_sq hn, one_mul] at hg
  rw [normalizedGauss_eq_gaussSum hn (by decide : 3 ≠ 0), map_div₀, Complex.conj_ofReal,
    ← mul_div_assoc, ← hg]

private lemma pairGauss_eq {b c : Ideal 𝓔} (hb : AwayFromSix b) (hc : AwayFromSix c)
    (h : IsCoprime b c) : pairGauss b c =
      (conj (sextic b (generator c)) * sextic c (generator b)) *
      (conj (sextic b (-1)) * conj (normalizedGauss b 1)) * normalizedGauss c 1 := by
  classical
  let := Ring.HasFiniteQuotients.finiteQuotient hb.1
  let := Fintype.ofFinite (𝓔 ⧸ b)
  let := Ring.HasFiniteQuotients.finiteQuotient hc.1
  let := Fintype.ofFinite (𝓔 ⧸ c)
  have ht := gaussSum_crt hb hc h (star (sexticChar hb)) (sexticChar hc)
  simp only [MulChar.star_apply, sexticChar_apply_mk, Complex.star_def] at ht
  unfold pairGauss pairCharacter normalizedGauss
  simp_rw [← quotientDifferentCharacter_apply]
  rw [ht, map_mul, Nat.cast_mul,
    Real.sqrt_mul (by positivity), Complex.ofReal_mul]
  simp only [finsum_eq_sum_of_fintype, pow_one, map_div₀, Complex.conj_ofReal]
  have hb' := gaussSum_star_left (sexticChar hb) (quotientDifferentCharacter b)
  have hm : sexticChar hb (-1) = sextic b (-1) := by
    simpa only [map_neg, map_one] using sexticChar_apply_mk hb (-1)
  rw [hm] at hb'
  simp only [gaussSum, MulChar.star_apply, Complex.star_def] at hb'
  rw [hb']
  change _ = _ * (_ * (conj (∑ x, sexticChar hb x * quotientDifferentCharacter b x) / _)) *
    ((∑ x, sexticChar hc x * quotientDifferentCharacter c x) / _)
  ring

private lemma moebius_sq {n : Ideal 𝓔} (hn : Starred n) : (idealMoebius n : ℂ) ^ 2 = 1 := by
  simp only [idealMoebius, ite_eq_left hn.2, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [pow_right_comm]
  simp

private lemma conj_cancel {z : ℂ} (hz : ‖z‖ = 1) : z * conj z = 1 := by
  rw [Complex.mul_conj', hz]; norm_num

private lemma moebius_mul_normalizedGauss (cube : DunnRadziwillGaussCube)
    {n : Ideal 𝓔} (hn : Starred n) :
    (idealMoebius n : ℂ) * normalizedGauss n 1 =
      conj (sextic n 4) * conj (gaussCoefficient n) * normalizedGauss n 3 := by
  have ha : angularFactor n * conj (angularFactor n) = 1 :=
    conj_cancel (norm_angularFactor_eq_one hn.1.1)
  have hg : gaussCoefficient n * angularFactor n = normalizedGauss n 2 := by
    rw [gaussCoefficient_eq, mul_comm, ← mul_assoc, ha, one_mul]
  have hc := gaussCoefficient_mul_angularFactor_cube cube hn.1
  rw [hg] at hc
  have hprod : sextic n 4 * gaussCoefficient n * normalizedGauss n 1 =
      (idealMoebius n : ℂ) * normalizedGauss n 3 := calc
    _ = gaussCoefficient n * (sextic n 4 * normalizedGauss n 1) := by ring
    _ = conj (angularFactor n) * normalizedGauss n 2 ^ 3 * normalizedGauss n 3 := by
      rw [normalizedGauss_duplication hn, gaussCoefficient_eq]; ring
    _ = _ := by rw [hc]; linear_combination (idealMoebius n : ℂ) * normalizedGauss n 3 * ha
  have h4 : IsCoprime n (span {(4 : 𝓔)}) := by
    have h2 := hn.1.2.of_isCoprime_of_dvd_right
      (span_singleton_dvd_span_singleton_iff_dvd.mpr (show (2 : 𝓔) ∣ 6 from ⟨3, by norm_num⟩))
    convert h2.pow_right (n := 2) using 1
    norm_num [span_singleton_pow]
  have hu := conj_cancel (norm_sextic_of_coprime hn.1 h4)
  have hv := conj_cancel (norm_gaussCoefficient_eq_one hn)
  calc
    _ = conj (sextic n 4) * conj (gaussCoefficient n) * (idealMoebius n : ℂ) *
        (sextic n 4 * gaussCoefficient n * normalizedGauss n 1) := by
      linear_combination -(idealMoebius n : ℂ) * normalizedGauss n 1 *
        (gaussCoefficient n * conj (gaussCoefficient n) * hu + hv)
    _ = _ := by
      rw [hprod]
      linear_combination conj (sextic n 4) * conj (gaussCoefficient n) * normalizedGauss n 3 *
        moebius_sq hn

private lemma pairGauss_direct (recip : DunnRadziwillReciprocity) (cube : DunnRadziwillGaussCube)
    {b c : Ideal 𝓔} (hb : Starred b) (hc : Starred c) (h : IsCoprime b c) :
    (idealMoebius b : ℂ) * idealMoebius c * pairGauss b c =
      gaussCoefficient b * conj (gaussCoefficient c) *
        (sextic b 4 * conj (sextic c 4) * normalizedGauss (b * c) 3) := by
  have h₁ := congrArg (starRingEnd ℂ) (moebius_mul_normalizedGauss cube hb)
  simp only [map_mul, map_intCast, Complex.conj_conj] at h₁
  have h₂ := moebius_mul_normalizedGauss cube hc
  rw [pairGauss_eq hb.1 hc.1 h, cross_cubic recip hb.1 hc.1 h,
    normalizedGauss_mul hb.1 hc.1 h (by decide : 3 ≠ 0)]
  let t := (sextic b (generator c) * sextic c (generator b)) ^ 3
  change _ * _ * (t * _ * _) = _ * (_ * (_ * _ * t))
  calc
    _ = t * conj (sextic b (-1)) * ((idealMoebius b : ℂ) * conj (normalizedGauss b 1)) *
        ((idealMoebius c : ℂ) * normalizedGauss c 1) := by ring
    _ = _ := by
      rw [h₁, h₂]
      linear_combination t * sextic b 4 * conj (sextic c 4) * gaussCoefficient b *
        conj (gaussCoefficient c) * normalizedGauss c 3 * quadraticGauss_conj hb.1

private def reduceModFour : Ray →+* 𝓔 ⧸ span {(4 : 𝓔)} :=
  Ideal.Quotient.factor (span_singleton_le_span_singleton.mpr ⟨18, by norm_num⟩)

/-- The two cubic symbols at the prime over two and the quadratic Gauss sum of the
product give the correction on residue classes modulo 72. -/
def pairedGaussCorrection (x y : Ray) : ℂ :=
  fourCorrection x * conj (fourCorrection y) * DeloupTuraev.quadraticRayValue (reduceModFour (x
    * y))

/-- The direct and reverse conversions use the same correction with swapped arguments. -/
theorem pairedGaussIdentities (recip : DunnRadziwillReciprocity) (cube : DunnRadziwillGaussCube)
    (quad : DeloupTuraevTheorem1) : PairedGaussIdentities := by
  have hQ {n : Ideal 𝓔} (hn : Starred n) :
      DeloupTuraev.quadraticRayValue (reduceModFour (ray n)) = normalizedGauss n 3 :=
    (DeloupTuraev.quadraticRayValue_mk quad hn.1.1).trans
      (normalizedGauss_three_eq_quadraticExponentialSum hn).symm
  have hA {b c : Ideal 𝓔} (hb : Starred b) (hc : Starred c) (h : IsCoprime b c) :
      (idealMoebius b : ℂ) * idealMoebius c * pairGauss b c =
        gaussCoefficient b * conj (gaussCoefficient c) * pairedGaussCorrection (ray b) (ray c) := by
    have hbc : Starred (b * c) := ⟨hb.1.mul hc.1, squarefree_mul_iff.mpr ⟨h.isRelPrime, hb.2, hc.2⟩⟩
    have hr : ray (b * c) = ray b * ray c := by
      simp [ray, generator_mul hb.1.coprime_three hc.1.coprime_three]
    simpa only [pairedGaussCorrection, fourCorrection_ray recip hb.1, fourCorrection_ray recip hc.1,
      ← hr, hQ hbc] using pairGauss_direct recip cube hb hc h
  refine ⟨pairedGaussCorrection, fun x y => pairedGaussCorrection y x, ?_⟩
  intro b c hb hc h
  refine ⟨hA hb hc h, ?_, gaussCoefficient_mul recip hb.1 hc.1 h⟩
  change _ = _ * pairedGaussCorrection (ray c) (ray b)
  have hrev := hA hc hb h.symm
  have hμ : ((idealMoebius c : ℂ) * idealMoebius b) ^ 2 = 1 := by
    rw [mul_pow, moebius_sq hb, moebius_sq hc, mul_one]
  have hb' := conj_cancel (norm_gaussCoefficient_eq_one hb)
  have hc' := conj_cancel (norm_gaussCoefficient_eq_one hc)
  calc
    _ = (idealMoebius c : ℂ) * idealMoebius b * gaussCoefficient b * conj (gaussCoefficient c) *
        ((idealMoebius c : ℂ) * idealMoebius b * pairGauss c b) := by
      linear_combination -gaussCoefficient b * conj (gaussCoefficient c) * pairGauss c b * hμ
    _ = _ := by
      rw [hrev]
      linear_combination (idealMoebius c : ℂ) * idealMoebius b * pairedGaussCorrection (ray c) (ray
        b) *
        (gaussCoefficient c * conj (gaussCoefficient c) * hb' + hc')

end Masullo.QRH.MeanSquare
