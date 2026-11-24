import WeilExplicit.Contour

/-! # Weil's explicit formula for Riemann zeta -/

namespace WeilExplicit

open WeilExplicit (transform weight)

open Complex MeasureTheory Real ArithmeticFunction

/-- Weil's explicit formula for twice continuously differentiable, compactly supported complex
tests, with the Fourier transform in angular frequency and the zeros counted with multiplicity. -/
theorem explicit_formula {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hs : HasCompactSupport k) :
    HasSum (fun ρ : stripZeros ↦ (zeroMult ρ : ℂ) * transform k (((ρ:ℂ)-1/2)/I))
      (transform k (I/2) + transform k (-I/2) -
        (∑' n : ℕ, ((vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))) +
        (1/(2*(π:ℂ))) * ∫ t : ℝ, transform k t *
          (((digamma (1/4+I*t/2)).re - Real.log π : ℝ) : ℂ)) := by
  let S := ∑' ρ : stripZeros, (zeroMult ρ : ℂ) * weight k ρ
  let P := ∑' n : ℕ, ((vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))
  let A := ∫ t : ℝ, transform k t * (((digamma (1/4+I*t/2)).re - Real.log π : ℝ) : ℂ)
  have hc := completed_contour hk hs
  obtain ⟨M,hM,h⟩ := pairedWeight_strip_decay hk hs
  have hw := (differentiable_pairedWeight hk.continuous hs).continuous
  simp_rw [WeilExplicit.completed_split_two, mul_add] at hc
  have hg := integrable_gamma_line hw hM h (x := 2) (by norm_num) le_rfl
  simp only [ofReal_ofNat] at hg
  rw [integral_add hg (integrable_zeta_line hw hM h), gamma_integral_eq hk hs] at hc
  have hp := prime_integral_eq hk hs (c := 2) (by norm_num)
  simp only [ofReal_ofNat, mul_neg, integral_neg] at hp
  let Z := ∫ t : ℝ, pairedWeight k (2+t*I)*logDeriv riemannZeta (2+t*I)
  change (2*(π:ℂ)) * (S-weight k 0-weight k 1) = A+Z at hc
  change -((2*(π:ℂ))⁻¹ * Z) = P at hp
  have h₀ : weight k 0 = transform k (I/2) := by
    unfold weight
    congr 1
    rw [div_I]
    ring
  have h₁ : weight k 1 = transform k (-I/2) := by
    unfold weight
    congr 1
    rw [div_I]
    ring
  change HasSum (fun ρ : stripZeros ↦ (zeroMult ρ : ℂ) * weight k ρ)
    (transform k (I/2) + transform k (-I/2) - P + (1/(2*(π:ℂ)))*A)
  convert! (summable_zero_transform hk hs).hasSum using 1
  change _ = S
  rw [← h₀, ← h₁]
  field_simp [Real.pi_ne_zero] at hp ⊢
  linear_combination -hc + hp

end WeilExplicit
