import Mathlib
import Masullo.Smoothed

/-!
# The ideal Möbius function of `ℚ(√-3)`

Let `𝓔 = 𝓞 (CyclotomicField 3 ℚ)`, the Eisenstein integers. `idealMoebius 𝔞` is `(-1) ^ r` on a
product of `r` distinct prime ideals and `0` on the other ideals, `⊥` included. `moebiusSum 𝔭 W D`
is `∑ μ(𝔞) W (N𝔞 / D)` over the nonzero ideals `𝔞` coprime to `6` and to `𝔭`.

The sum of `idealMoebius` over the ideals of norm `n` is `eisensteinMoebius n = (μ ∗ χ₃μ) n`
(`sum_idealMoebius_absNorm_eq`). Both sides are multiplicative, and the local polynomials are
`(1 - T)²` at the split primes `p ≡ 1 mod 3`, `1 - T²` at the inert primes `p ≡ 2 mod 3` and
`1 - T` at the ramified prime `3`. The splitting comes from
`IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd` and its companions.
-/

open NumberField Ideal UniqueFactorizationMonoid

namespace Masullo.QRH

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The ideal Möbius function: `(-1) ^ r` on a product of `r` distinct prime ideals, else `0`. -/
noncomputable def idealMoebius (𝔞 : Ideal 𝓔) : ℤ :=
  open Classical in
  if Squarefree 𝔞 then (-1) ^ Multiset.card (normalizedFactors 𝔞) else 0

/-- `∑ μ(𝔞) W (N𝔞 / D)` over the nonzero ideals `𝔞` coprime to `6` and to `𝔭`. -/
noncomputable def moebiusSum (𝔭 : Ideal 𝓔) (W : ℝ → ℂ) (D : ℝ) : ℂ :=
  open Classical in
  ∑' 𝔞 : Ideal 𝓔, if 𝔞 ≠ ⊥ ∧ IsCoprime 𝔞 (span {6}) ∧ IsCoprime 𝔞 𝔭 then
    (idealMoebius 𝔞 : ℂ) * W (absNorm 𝔞 / D) else 0

/-- The sum of `idealMoebius` over the ideals of norm `n` is `(μ ∗ χ₃μ) n`. -/
theorem sum_idealMoebius_absNorm_eq (n : ℕ) :
    ∑ 𝔞 ∈ (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓔) n).toFinset,
      (idealMoebius 𝔞 : ℂ) = Smoothed.eisensteinMoebius n := by
  sorry

end Masullo.QRH
