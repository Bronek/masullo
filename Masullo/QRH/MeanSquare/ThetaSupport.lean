import Masullo.QRH.MeanSquare.Theta
import Masullo.QRH.MeanSquare.GaussPhase
import Masullo.QRH.MeanSquare.Residue

/-! # Ramified support of Patterson's coefficients -/

noncomputable section

open NumberField

namespace Masullo.QRH.MeanSquare

local notation "K" => CyclotomicField 3 ℚ
local notation "𝓔" => 𝓞 K

private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

theorem eisLambda_prime : Prime eisLambda := by
  have hp : Prime (eisOmega - 1) := (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'
  have hω : eisOmega ^ 2 + eisOmega + 1 = 0 :=
    IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one (IsCyclotomicExtension.zeta_spec 3 ℚ K)
  have hassoc : Associated (eisOmega - 1) eisLambda := by
    refine ⟨-(omega_primitive.isUnit (by decide : 3 ≠ 0)).unit, ?_⟩
    change (eisOmega - 1) * -eisOmega = 1 + 2 * eisOmega
    linear_combination -hω
  exact hassoc.prime_iff.mp hp

theorem eisPrimary.lambda_not_dvd {a : 𝓔} (h : eisPrimary a) : ¬ eisLambda ∣ a := by
  intro ha
  have h3 : eisLambda ∣ (3 : 𝓔) := ⟨-eisLambda, by rw [mul_neg, ← sq, eisLambda_sq, neg_neg]⟩
  have hd := dvd_sub ha (h3.trans h)
  exact eisLambda_prime.not_isUnit (isUnit_of_dvd_one (by simpa using hd))

/-- Exponent of the different in the integral numerator at the infinity cusp. -/
def PattersonLayer.lambdaExponent : PattersonLayer → ℕ
  | .unshifted j => 3 * j
  | .shifted k _ => 3 * k + 2

/-- The cubic unit in the numerator of a signed frequency, before attaching its sign. -/
def PattersonLayer.unitFactor : PattersonLayer → 𝓔
  | .unshifted _ => 1
  | .shifted _ r => eisOmega ^ (r : ℕ)

theorem PattersonLayer.isUnit_unitFactor (l : PattersonLayer) : IsUnit l.unitFactor := by
  cases l with
  | unshifted => exact isUnit_one
  | shifted _ r => exact (omega_primitive.isUnit (by decide)).pow r.val

/-- Integral index of the frequency after multiplication by `λ³`. -/
def PattersonRow.numerator (r : PattersonRow) : 𝓔 :=
  eisLambda ^ r.layer.lambdaExponent * (r.layer.unitFactor * r.c * r.d ^ 3)

theorem PattersonRow.frequency_eq_div (r : PattersonRow) :
    r.frequency = eisEmbedding r.numerator / eisEmbedding eisLambda ^ 3 := by
  have h : eisEmbedding eisLambda ≠ 0 :=
    fun he => eisLambda_prime.ne_zero (eisEmbedding_injective (he.trans (map_zero _).symm))
  have hexp (n : ℕ) : eisEmbedding eisLambda ^ ((n : ℤ) - 3) =
      eisEmbedding eisLambda ^ n / eisEmbedding eisLambda ^ 3 :=
    zpow_natCast_sub_natCast₀ h n 3
  obtain ⟨l,c,d,hc,hd,hs⟩ := r
  cases l with
  | unshifted j =>
    simp only [PattersonRow.frequency, PattersonRow.numerator, PattersonLayer.lambdaExponent,
      PattersonLayer.unitFactor, one_mul, map_mul, map_pow]
    rw [show 3 * (j : ℤ) = ((3 * j : ℕ) : ℤ) by push_cast; ring, hexp]
    ring
  | shifted k i =>
    simp only [PattersonRow.frequency, PattersonRow.numerator, PattersonLayer.lambdaExponent,
      PattersonLayer.unitFactor, map_mul, map_pow]
    rw [show 3*(k : ℤ) - 1 = ((3*k + 2 : ℕ) : ℤ) - 3 by push_cast; ring, hexp]
    ring

theorem PattersonRow.emultiplicity_numerator (r : PattersonRow) :
    emultiplicity eisLambda r.numerator = r.layer.lambdaExponent := by
  have hu : ¬ eisLambda ∣ r.layer.unitFactor :=
    fun h => eisLambda_prime.not_isUnit (isUnit_of_dvd_unit h r.layer.isUnit_unitFactor)
  have hd : ¬ eisLambda ∣ r.d ^ 3 := fun h => r.primary_d.lambda_not_dvd
    (eisLambda_prime.dvd_of_dvd_pow h)
  simp only [PattersonRow.numerator, emultiplicity_mul eisLambda_prime,
    emultiplicity_pow_self_of_prime eisLambda_prime, emultiplicity_eq_zero.mpr hu,
    emultiplicity_eq_zero.mpr r.primary_c.lambda_not_dvd, emultiplicity_eq_zero.mpr hd,
    add_zero]

/-- The numerator of a supported frequency never has different exponent congruent to one
modulo three. -/
theorem PattersonCoefficients.zero_of_lambda_exponent {τ : ℂ → ℂ} (hτ : PattersonCoefficients τ)
    {m : 𝓔} {j : ℕ} (h₁ : eisLambda ^ (3*j+1) ∣ m) (h₂ : ¬ eisLambda ^ (3*j+2) ∣ m) :
    τ (eisEmbedding m / eisEmbedding eisLambda ^ 3) = 0 := by
  have hLambda : eisEmbedding eisLambda ≠ 0 :=
    fun he => eisLambda_prime.ne_zero (eisEmbedding_injective (he.trans (map_zero _).symm))
  have hval : emultiplicity eisLambda m = ((3*j+1 : ℕ) : ℕ∞) := emultiplicity_eq_coe.mpr ⟨h₁, h₂⟩
  have hn (r : PattersonRow) : r.layer.lambdaExponent ≠ 3*j+1 := by
    cases r.layer <;> simp only [PattersonLayer.lambdaExponent] <;> omega
  apply hτ.2
  intro r
  rw [r.frequency_eq_div, ← neg_div]
  constructor
  · intro e
    have he := eisEmbedding_injective ((div_left_inj₀ (pow_ne_zero 3 hLambda)).mp e)
    rw [he, r.emultiplicity_numerator] at hval
    exact hn r (by exact_mod_cast hval)
  · intro e
    rw [← map_neg] at e
    have he := eisEmbedding_injective ((div_left_inj₀ (pow_ne_zero 3 hLambda)).mp e)
    rw [he, emultiplicity_neg, r.emultiplicity_numerator] at hval
    exact hn r (by exact_mod_cast hval)

theorem PattersonCoefficients.zero_of_lambda_four {τ : ℂ → ℂ} (hτ : PattersonCoefficients τ)
    {m : 𝓔} (h₄ : eisLambda ^ 4 ∣ m) (h₅ : ¬ eisLambda ^ 5 ∣ m) :
    τ (eisEmbedding m / eisEmbedding eisLambda ^ 3) = 0 :=
  hτ.zero_of_lambda_exponent (j := 1) h₄ h₅

/-- Removing the denominator in the layer of exponent three gives precisely the
unshifted table entry at `cd³`. -/
theorem PattersonRow.frequency_of_lambdaExponent_three (r : PattersonRow)
    (h : r.layer.lambdaExponent = 3) : r.frequency = eisEmbedding (r.c * r.d ^ 3) := by
  obtain ⟨l, c, d, hc, hd, hs⟩ := r
  cases l with
  | unshifted j =>
    change 3 * j = 3 at h
    obtain rfl : j = 1 := by omega
    norm_num [PattersonRow.frequency]
  | shifted k i =>
    change 3 * k + 2 = 3 at h
    omega

/-- Every supported integral frequency prime to the different is a signed primary
cube times a squarefree primary element. -/
theorem PattersonCoefficients.exists_primary_cube {τ : ℂ → ℂ} (hτ : PattersonCoefficients τ)
    {m : 𝓔} (hm : ¬ eisLambda ∣ m) (ht : τ (eisEmbedding m) ≠ 0) :
    ∃ c d : 𝓔, eisPrimary c ∧ eisPrimary d ∧ Squarefree c ∧
      (m = c * d ^ 3 ∨ m = -(c * d ^ 3)) := by
  classical
  obtain ⟨r, hr⟩ : ∃ r : PattersonRow, eisEmbedding m = r.frequency ∨ eisEmbedding m =
    -r.frequency := by
    by_contra! h
    exact ht (hτ.2 _ h)
  have hLambda : eisEmbedding eisLambda ≠ 0 :=
    fun he => eisLambda_prime.ne_zero (eisEmbedding_injective (he.trans (map_zero _).symm))
  have h₃ : emultiplicity eisLambda (m * eisLambda ^ 3) = 3 := by
    rw [emultiplicity_mul eisLambda_prime, emultiplicity_eq_zero.mpr hm,
      emultiplicity_pow_self_of_prime eisLambda_prime, zero_add]
    rfl
  have hexp : r.layer.lambdaExponent = 3 := by
    rw [r.frequency_eq_div, ← neg_div] at hr
    rcases hr with h | h
    · have he := (eq_div_iff (pow_ne_zero 3 hLambda)).mp h
      rw [← map_pow, ← map_mul] at he
      rw [eisEmbedding_injective he, r.emultiplicity_numerator] at h₃
      exact_mod_cast h₃
    · have he := (eq_div_iff (pow_ne_zero 3 hLambda)).mp h
      rw [← map_pow, ← map_mul, ← map_neg] at he
      rw [eisEmbedding_injective he, emultiplicity_neg, r.emultiplicity_numerator] at h₃
      exact_mod_cast h₃
  rw [r.frequency_of_lambdaExponent_three hexp, ← map_neg] at hr
  exact ⟨r.c, r.d, r.primary_c, r.primary_d, r.squarefree_c,
    hr.imp (fun h => eisEmbedding_injective h) (fun h => eisEmbedding_injective h)⟩

end Masullo.QRH.MeanSquare
