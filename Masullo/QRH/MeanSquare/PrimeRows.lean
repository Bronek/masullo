import Masullo.QRH.MeanSquare.Forms
import Masullo.QRH.MeanSquare.Residue

/-! # Restricting the full Möbius mean square to prime sixth powers -/

noncomputable section

open NumberField Ideal
open scoped ContDiff

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The Möbius row in the original family, with trivial auxiliary Hecke character. -/
def moebiusRow (W : ℝ → ℂ) (D : ℝ) (y : 𝓔) : ℂ := open Classical in
  ∑' n : Ideal 𝓔, if AwayFromSix n then
    (idealMoebius n : ℂ) * sextic n y * W (absNorm n / D) else 0

/-- The fixed-test consequence of Proposition 3.1, (3.1), p. 11 of OpenAI,
*The Quasi-Riemann Hypothesis* (5 October 2026), with trivial twist and bad
primes above six. This is an intermediate target of the first Poisson reduction. -/
def FullRowEstimate : Prop :=
  ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W → HasCompactSupport W → tsupport W ⊆ Set.Ioi 0 →
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 10 → ∀ ε > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ D : ℝ, 2 ≤ D →
      ∑ k ∈ elementRows (D ^ (1 + θ)), ‖moebiusRow W D k‖ ^ 2 ≤ C * D ^ (2 + θ + ε)

open Classical in
theorem moebiusRow_sixth
    (p : Ideal 𝓔) (W : ℝ → ℂ) (D : ℝ) :
    moebiusRow W D (generator p ^ 6) = moebiusSum p W D := by
  unfold moebiusRow moebiusSum
  apply tsum_congr
  intro n
  by_cases h : AwayFromSix n
  · rw [ite_eq_left h, sextic, powerResidueSymbol_sixth h.1 h.2, span_generator]
    by_cases hnp : IsCoprime n p
    · rw [ite_eq_left hnp, ite_eq_left ⟨h.1, h.2, hnp⟩, map_one, mul_one]
    · rw [ite_eq_right hnp, ite_eq_right (fun hh => hnp hh.2.2), map_zero, mul_zero, zero_mul]
  · rw [ite_eq_right h, ite_eq_right (fun hh => h ⟨hh.1, hh.2.1⟩)]

open Classical in
theorem meanSquareA_of_fullRows
    (hfull : FullRowEstimate) : MeanSquareA := by
  intro W hW hc hs δ hδ
  let θ := min (1 / 10 : ℝ) (δ / 2)
  have hθ : 0 < θ := lt_min (by norm_num) (by positivity)
  obtain ⟨C, hC, h⟩ := hfull W hW hc hs θ hθ (min_le_left ..) (δ / 2) (by positivity)
  refine ⟨C, fun D hD => ?_⟩
  have hD₁ : 1 ≤ D := by linarith
  have hDH : D ≤ D ^ (1 + θ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hD₁ (show (1 : ℝ) ≤ 1 + θ by linarith)
  calc ∑' p : primesUpTo (D ^ (1 / 6 : ℝ)), ‖moebiusSum p W D‖ ^ 2
      = ∑' p : primesUpTo (D ^ (1 / 6 : ℝ)), ‖moebiusRow W D (generator p ^ 6)‖ ^ 2 := by
        simp only [moebiusRow_sixth]
    _ ≤ _ := primeSixthRows_le (by linarith : 0 < D) (moebiusRow W D)
    _ ≤ ∑ k ∈ elementRows (D ^ (1 + θ)), ‖moebiusRow W D k‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => sq_nonneg _)
        intro k hk
        have hk' := (mem_elementRows (by linarith : 0 ≤ D)).mp hk
        exact (mem_elementRows (by positivity)).mpr ⟨hk'.1, hk'.2.trans hDH⟩
    _ ≤ _ := h D hD
    _ ≤ C * D ^ (2 + δ) := by
        apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hD₁ ?_) hC
        linarith [show θ ≤ δ / 2 from min_le_right ..]

end Masullo.QRH.MeanSquare
