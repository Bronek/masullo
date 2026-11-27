import Masullo.QRH.IdealMoebius

/-!
# From the mean square (A) to the trace identity

Let `𝓔 = 𝓞 (CyclotomicField 3 ℚ)`. `MeanSquareA` is estimate (A), a consequence of
Proposition 3.1 of OpenAI, *The Quasi-Riemann Hypothesis* (5 October 2026): for every smooth `W` with compact support in `(0, ∞)` and every
`δ > 0`,

  `∑_{𝔭 ∤ 6, N𝔭 ≤ D ^ (1/6)} ‖M_𝔭(W, D)‖² ≪_{W,δ} D ^ (2 + δ)`  for `D ≥ 2`,

over the nonzero prime ideals `𝔭`, where `M_𝔭(W, D) = moebiusSum 𝔭 W D`. It is a hypothesis
here, not a theorem.

From it, `smoothedBound_of_meanSquareA` gives `SmoothedBound eisensteinMoebius β` for every
`β > 23/24`, and `hasTrace_of_meanSquareA` gives the trace identity at every width `a > 11/24`.

For each rational prime `5 ≤ p ≤ D ^ (1/12)` take one prime ideal `q_p` above `p`. Its norm is `p`
or `p²`, at most `D ^ (1/6)`, so (A) bounds `∑_p ‖M_{q_p}‖²`. Removing the multiples of `q_p`
changes the full sum `M = M_⊤` by `O_W(D / p)`. Chebyshev's bounds give `≫ Y / log Y` primes in
`(Y / C, Y]`, and averaging `‖M‖² ≤ 2 ‖M_{q_p}‖² + 2 ‖M - M_{q_p}‖²` over them with
`Y = D ^ (1/12)` gives `M ≪ D ^ (23/24 + ε)`. Adding back the ideals above `2` and `3` and
grouping by norm (`sum_idealMoebius_absNorm_eq`) turns this into the smoothed bound. Rational
primes replace the prime ideals with `N𝔭 ∈ (Y / C, Y]`, `Y = D ^ (1/6)`, of the source, which
would give `11/12`, so no prime ideal theorem over `𝓔` is needed.
-/

open NumberField Ideal
open scoped ContDiff

namespace Masullo.QRH

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The nonzero prime ideals `𝔭 ∤ 6` with `N𝔭 ≤ X`. -/
def primesUpTo (X : ℝ) : Set (Ideal 𝓔) :=
  {𝔭 | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ 𝔭 ∣ span {6} ∧ (absNorm 𝔭 : ℝ) ≤ X}

/-- Estimate (A): for every smooth `W` with compact support in `(0, ∞)` and every `δ > 0`,
`∑_{𝔭 ∤ 6, N𝔭 ≤ D ^ (1/6)} ‖M_𝔭(W, D)‖² ≤ C D ^ (2 + δ)` for `D ≥ 2`, with `C` depending on
`W` and `δ`. -/
def MeanSquareA : Prop :=
  ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W → HasCompactSupport W → tsupport W ⊆ Set.Ioi 0 →
    ∀ δ : ℝ, 0 < δ → ∃ C, ∀ D : ℝ, 2 ≤ D →
      ∑' 𝔭 : primesUpTo (D ^ (1 / 6 : ℝ)), ‖moebiusSum 𝔭 W D‖ ^ 2 ≤ C * D ^ (2 + δ)

/-- (A) gives the smoothed bound for `μ ∗ χ₃μ` at every exponent `β > 23/24`. -/
theorem smoothedBound_of_meanSquareA (h : MeanSquareA) {β : ℝ} (hβ : 23 / 24 < β) :
    Smoothed.SmoothedBound Smoothed.eisensteinMoebius β := by
  sorry

/-- (A) gives the trace identity at every width `a > 11/24`. -/
theorem hasTrace_of_meanSquareA (h : MeanSquareA) {a : ℝ} (ha : 11 / 24 < a)
    (φ : TestFunction) :
    Trace.HasTrace (Trace.induced (by linarith : (0 : ℝ) < a) φ) φ.efFunctional :=
  Smoothed.hasTrace_of_smoothedBound (β := (a + 1 / 2 + 23 / 24) / 2) (by linarith) _
    (by linarith) (smoothedBound_of_meanSquareA h (by linarith)) φ

end Masullo.QRH
