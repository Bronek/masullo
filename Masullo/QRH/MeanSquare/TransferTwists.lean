import Masullo.QRH.MeanSquare.TransferPassBound
import Masullo.QRH.MeanSquare.GaussNorm
import Masullo.QRH.MeanSquare.OffDiagonal

/-!
# The weights and twists of the two transfer passes

The first pass runs with the weight `starredGauss` and the twist `firstTwist`; its Gauss
sums convert into the Möbius weight `moebiusTwist`. The second pass runs with `moebiusTwist`
and the twist `secondTwist`; its Gauss sums convert into `conjGauss`.

* `twistMul_starredGauss`, `twistMul_moebiusTwist`, `twistMul_conjGauss`,
  `twistMul_firstTwist`, `twistMul_secondTwist`: the multiplicativity across coprime starred
  splits.
* `exists_gaussConversion_first`, `exists_gaussConversion_second`: the two conversions of the
  Gauss sums, from `PairedGaussIdentities`.
-/

noncomputable section

open NumberField Ideal
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The Gauss coefficient, restricted to starred ideals. -/
def starredGauss (n : Ideal 𝓔) : ℂ := open Classical in
  if Starred n then gaussCoefficient n else 0

/-- The conjugate of `starredGauss`. -/
def conjGauss (n : Ideal 𝓔) : ℂ := conj (starredGauss n)

/-- The Möbius function as a weight. -/
def moebiusTwist (n : Ideal 𝓔) : ℂ := (idealMoebius n : ℂ)

/-- The twist of the first pass: the ray character and the sextic character of `f⁴`. -/
def firstTwist (ξ : RayCharacter) (f n : Ideal 𝓔) : ℂ :=
  ξ (Ideal.Quotient.mk _ (generator n)) * sextic n (generator f ^ 4)

/-- The twist of the second pass: coprimality to `c` and the conjugate of the first-pass dual
twist by `ξ ξ'` and `g⁴ e`. -/
def secondTwist (ξ ξ' : RayCharacter) (g e c n : Ideal 𝓔) : ℂ := open Classical in
  if IsCoprime c n then
    conj (ξ (Ideal.Quotient.mk _ (generator n)) * ξ' (Ideal.Quotient.mk _ (generator n)) *
      sextic n (generator g ^ 4 * generator e))
  else 0

lemma norm_starredGauss_le (n : Ideal 𝓔) : ‖starredGauss n‖ ≤ 1 := by
  unfold starredGauss
  split_ifs with h
  · exact gaussCoefficientBound n h
  · simp

lemma norm_conjGauss_le (n : Ideal 𝓔) : ‖conjGauss n‖ ≤ 1 := by
  simpa [conjGauss] using norm_starredGauss_le n

lemma norm_moebiusTwist_le (n : Ideal 𝓔) : ‖moebiusTwist n‖ ≤ 1 := by
  exact norm_idealMoebius_le n

lemma norm_firstTwist_le (ξ : RayCharacter) (f n : Ideal 𝓔) : ‖firstTwist ξ f n‖ ≤ 1 := by
  unfold firstTwist
  rw [norm_mul]
  exact mul_le_one_of_le (norm_rayCharacter_le _ _) (norm_nonneg _) (norm_sextic_le_one _ _)

lemma norm_secondTwist_le (ξ ξ' : RayCharacter) (g e c n : Ideal 𝓔) :
    ‖secondTwist ξ ξ' g e c n‖ ≤ 1 := by
  unfold secondTwist
  split_ifs
  · rw [Complex.norm_conj, norm_mul, norm_mul]
    have h1 := norm_rayCharacter_le ξ (Ideal.Quotient.mk _ (generator n))
    have h2 := norm_rayCharacter_le ξ' (Ideal.Quotient.mk _ (generator n))
    have h3 := norm_sextic_le_one n (generator g ^ 4 * generator e)
    have h4 : ‖ξ (Ideal.Quotient.mk _ (generator n))‖ *
        ‖ξ' (Ideal.Quotient.mk _ (generator n))‖ ≤ 1 :=
      mul_le_one_of_le h1 (norm_nonneg _) h2
    exact mul_le_one_of_le h4 (norm_nonneg _) h3
  · simp

lemma sextic_pow_six {n : Ideal 𝓔} (hn : AwayFromSix n) {a : 𝓔}
    (ha : IsCoprime n (span {a})) : sextic n a ^ 6 = 1 := by
  simp only [sextic, ← map_pow, powerResidueSymbol_six_pow_six hn.1 hn.2, ite_eq_left ha, map_one]

lemma twistMul_starredGauss (hpg : PairedGaussIdentities) : TwistMul starredGauss 4 := by
  obtain ⟨A, B, H⟩ := hpg
  intro g z hg hz h
  have hgz := hg.mul_of_isCoprime hz h
  simp only [starredGauss, hg, hz, hgz, ite_true]
  exact (H g z hg hz h).2.2

lemma twistMul_conjGauss (hpg : PairedGaussIdentities) : TwistMul conjGauss 2 := by
  obtain ⟨A, B, H⟩ := hpg
  intro g z hg hz h
  have hgz := hg.mul_of_isCoprime hz h
  have hc : IsCoprime z (span {generator g}) := by rwa [span_generator, isCoprime_comm]
  have h5 := conj_sextic_eq_pow_five hz.1 hc
  have h6 := sextic_pow_six hz.1 hc
  unfold conjGauss
  simp only [starredGauss, hg, hz, hgz, ite_true]
  rw [(H g z hg hz h).2.2, map_mul, map_mul, map_pow, h5, ← pow_mul]
  linear_combination (conj (gaussCoefficient g) * conj (gaussCoefficient z)) *
    (sextic z (generator g) ^ 2 * (sextic z (generator g) ^ 12 + sextic z (generator g) ^ 6 + 1))
    * h6

lemma twistMul_moebiusTwist : TwistMul moebiusTwist 0 := by
  intro g z hg hz h
  unfold moebiusTwist
  rw [idealMoebius_mul h]
  push_cast
  simp

lemma twistMul_firstTwist (ξ : RayCharacter) (f : Ideal 𝓔) : TwistMul (firstTwist ξ f) 0 := by
  intro g z hg hz h
  unfold firstTwist
  rw [generator_mul hg.1.coprime_three hz.1.coprime_three, map_mul, map_mul ξ,
    sextic_mul_right]
  simp only [pow_zero, mul_one]
  ring

lemma twistMul_secondTwist (ξ ξ' : RayCharacter) (g e c : Ideal 𝓔) :
    TwistMul (secondTwist ξ ξ' g e c) 0 := by
  intro g' z hg hz h
  unfold secondTwist
  rw [generator_mul hg.1.coprime_three hz.1.coprime_three]
  by_cases h1 : IsCoprime c g' <;> by_cases h2 : IsCoprime c z
  · simp [h1, h2, IsCoprime.mul_right h1 h2]
    rw [sextic_mul_right]
    simp only [map_mul]
    ring
  · simp [h2, mt IsCoprime.of_mul_right_right h2]
  · simp [h1, mt IsCoprime.of_mul_right_left h1]
  · simp [h1, mt IsCoprime.of_mul_right_left h1]

theorem exists_gaussConversion_first (hpg : PairedGaussIdentities) :
    ∃ Corr, GaussConversion starredGauss moebiusTwist Corr := by
  obtain ⟨A, B, H⟩ := hpg
  refine ⟨B, fun z₁ z₂ h₁ h₂ h => ?_⟩
  have := (H z₁ z₂ h₁ h₂ h).2.1
  simp only [starredGauss, moebiusTwist, h₁, h₂, ite_true]
  exact this

theorem exists_gaussConversion_second (hpg : PairedGaussIdentities) :
    ∃ Corr, GaussConversion moebiusTwist conjGauss Corr := by
  obtain ⟨A, B, H⟩ := hpg
  refine ⟨fun x y => A y x, fun z₁ z₂ h₁ h₂ h => ?_⟩
  have := (H z₂ z₁ h₂ h₁ h.symm).1
  simp only [conjGauss, starredGauss, moebiusTwist, h₁, h₂, ite_true, map_intCast,
    Complex.conj_conj]
  rw [mul_comm] at this
  linear_combination this

end Masullo.QRH.MeanSquare
