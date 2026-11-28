import Masullo.QRH.MeanSquare.TransferPass

/-!
# The arithmetic factor of a Poisson pass

A Poisson pass of `TransferEstimate` acts on columns `κ(n) φ(n) V(Nn/ℓ)`. The weight `κ` is
multiplicative up to a sextic twist (`TwistMul`), and a Gauss conversion (`GaussConversion`)
turns `κ(z₁) conj κ(z₂) pairGauss z₂ z₁` into `κ'(z₁) conj κ'(z₂)` times a ray correction.

* `mul_pairGauss_eq_splitSummand`: on a gcd split `(g, z₁, z₂)` the coefficients of the two
  columns and the Gauss sum form `splitSummand`.
* `splitSummand_mul_eq`: at `z₁ = v x₁`, `z₂ = v x₂`, with the ray correction expanded in ray
  characters, the summand times the dual characters at `e°` and `h` is a combination of a row
  factor `passRowFactor` and two dual columns `dualCoeff`.
-/

noncomputable section

open NumberField Ideal
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

local notation "Q₇₂" => 𝓔 ⧸ span {(72 : 𝓔)}

/-- Multiplicativity across coprime starred splits up to the twist `χ_z(g°)^p`. -/
def TwistMul (κ : Ideal 𝓔 → ℂ) (p : ℕ) : Prop :=
  ∀ g z : Ideal 𝓔, Starred g → Starred z → IsCoprime g z →
    κ (g * z) = κ g * κ z * sextic z (generator g) ^ p

/-- The conversion of `κ(z₁) conj κ(z₂) pairGauss z₂ z₁` into a weight `κ'` and a correction
depending on the generators modulo `72`. -/
def GaussConversion (κ κ' : Ideal 𝓔 → ℂ) (Corr : Q₇₂ → Q₇₂ → ℂ) : Prop :=
  ∀ z₁ z₂ : Ideal 𝓔, Starred z₁ → Starred z₂ → IsCoprime z₁ z₂ →
    κ z₁ * conj (κ z₂) * pairGauss z₂ z₁ =
      κ' z₁ * conj (κ' z₂) * Corr (Ideal.Quotient.mk _ (generator z₁))
        (Ideal.Quotient.mk _ (generator z₂))

/-- The arithmetic summand of the gcd split `(g, z₁, z₂)` after the Gauss conversion. -/
def splitSummand (κ κ' φ : Ideal 𝓔 → ℂ) (p : ℕ) (Corr : Q₇₂ → Q₇₂ → ℂ)
    (g z₁ z₂ : Ideal 𝓔) : ℂ :=
  κ g * conj (κ g) * (φ g * conj (φ g)) *
    (sextic z₁ (generator g) ^ p * conj (sextic z₂ (generator g) ^ p)) *
    (κ' z₁ * conj (κ' z₂) * Corr (Ideal.Quotient.mk _ (generator z₁))
      (Ideal.Quotient.mk _ (generator z₂))) * (φ z₁ * conj (φ z₂))

/-- The coefficient of a dual column at `x`, for the row `(g, e, v, h)` and ray character `ξ`. -/
def dualCoeff (κ' φ : Ideal 𝓔 → ℂ) (p p' : ℕ) (ξ : RayCharacter) (g e v : Ideal 𝓔) (h : 𝓔)
    (x : Ideal 𝓔) : ℂ :=
  κ' x * ξ (Ideal.Quotient.mk _ (generator x)) * φ x * sextic x (generator g) ^ p *
    sextic x (generator v) ^ p' * sextic x (generator e) * conj (sextic x h)

/-- The factor of a dual row `(g, e, v, h)` for the ray characters `ξ, η`. -/
def passRowFactor (κ κ' φ : Ideal 𝓔 → ℂ) (p : ℕ) (ξ η : RayCharacter) (g e v : Ideal 𝓔)
    (h : 𝓔) : ℂ :=
  κ g * conj (κ g) * (φ g * conj (φ g)) * (κ' v * conj (κ' v)) * (φ v * conj (φ v)) *
    (ξ (Ideal.Quotient.mk _ (generator v)) * conj (η (Ideal.Quotient.mk _ (generator v)))) *
    (sextic v (generator g) ^ p * conj (sextic v (generator g) ^ p)) *
    (sextic v (generator e) * conj (sextic v (generator e))) *
    (sextic v h * conj (sextic v h))

/-- On a gcd split the two column coefficients and the Gauss sum form `splitSummand`. -/
theorem mul_pairGauss_eq_splitSummand {κ κ' φ : Ideal 𝓔 → ℂ} {p : ℕ}
    {Corr : Q₇₂ → Q₇₂ → ℂ} (hκ : TwistMul κ p) (hφ : TwistMul φ 0)
    (hconv : GaussConversion κ κ' Corr) {g z₁ z₂ : Ideal 𝓔} (ht : IsGcdSplit (g, z₁, z₂)) :
    κ (g * z₁) * φ (g * z₁) * conj (κ (g * z₂) * φ (g * z₂)) * pairGauss z₂ z₁ =
      splitSummand κ κ' φ p Corr g z₁ z₂ := by
  obtain ⟨hg, h1, h2, h12, hg12⟩ := ht
  have hg2 : IsCoprime g z₂ := hg12.of_mul_right_left
  have hg1 : IsCoprime g z₁ := hg12.of_mul_right_right
  have hc := hconv z₁ z₂ h1 h2 h12
  rw [hκ g z₁ hg h1 hg1, hκ g z₂ hg h2 hg2, hφ g z₁ hg h1 hg1, hφ g z₂ hg h2 hg2]
  simp only [splitSummand, pow_zero, mul_one, map_mul, map_pow]
  linear_combination (conj (κ g) * κ g * (φ g * conj (φ g)) *
    (sextic z₁ (generator g) ^ p * conj (sextic z₂ (generator g)) ^ p) *
    (φ z₁ * conj (φ z₂))) * hc

/-- The summand at `z₁ = v x₁`, `z₂ = v x₂` with the dual characters at `e°` and `h`. -/
theorem splitSummand_mul_eq (hres : ResidueMultiplicative) {κ κ' φ : Ideal 𝓔 → ℂ} {p p' : ℕ}
    (hκ' : TwistMul κ' p') (hφ : TwistMul φ 0) {Corr : Q₇₂ → Q₇₂ → ℂ}
    {α : RayCharacter → RayCharacter → ℂ}
    (hα : ∀ x y : Q₇₂, IsUnit x → IsUnit y → Corr x y = ∑ ξ, ∑ η, α ξ η * ξ x * conj (η y))
    {g e v x₁ x₂ : Ideal 𝓔} (hv : Starred v) (h₁ : Starred x₁) (h₂ : Starred x₂)
    (hv₁ : IsCoprime v x₁) (hv₂ : IsCoprime v x₂) (h : 𝓔) :
    splitSummand κ κ' φ p Corr g (v * x₁) (v * x₂) *
        (pairCharacter (v * x₂) (v * x₁) (generator e) *
          conj (pairCharacter (v * x₂) (v * x₁) h)) =
      ∑ ξ, ∑ η, α ξ η * passRowFactor κ κ' φ p ξ η g e v h *
        (dualCoeff κ' φ p p' ξ g e v h x₁ * conj (dualCoeff κ' φ p p' η g e v h x₂)) := by
  have h3 : ∀ {n : Ideal 𝓔}, AwayFromSix n → IsCoprime n (span {3}) := fun hn =>
    hn.coprime_three
  have hgen : ∀ {n : Ideal 𝓔}, AwayFromSix n → generator (v * n) = generator v * generator n :=
    fun hn => hres.generator_mul (h3 hv.1) (h3 hn)
  rw [splitSummand, hκ' v x₁ hv h₁ hv₁, hκ' v x₂ hv h₂ hv₂, hφ v x₁ hv h₁ hv₁,
    hφ v x₂ hv h₂ hv₂,
    hα _ _ (isUnit_mk_generator (hv.1.mul h₁.1)) (isUnit_mk_generator (hv.1.mul h₂.1)),
    hgen h₁.1, hgen h₂.1]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  refine Finset.sum_congr rfl fun η _ => ?_
  simp only [passRowFactor, dualCoeff, pairCharacter, sextic_mul_right, pow_zero, mul_one,
    map_mul, map_pow, Complex.conj_conj]
  ring

end Masullo.QRH.MeanSquare
