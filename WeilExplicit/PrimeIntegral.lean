import WeilExplicit.Inversion
import Mathlib.NumberTheory.LSeries.Dirichlet

/-! # Evaluation of the von Mangoldt integral by Fourier inversion -/

namespace WeilExplicit

open WeilExplicit (transform weight)

open Complex Real MeasureTheory ArithmeticFunction

private noncomputable abbrev mangoldt (n : ℕ) : ℂ := (vonMangoldt n : ℝ)

private theorem term_on_line (n : ℕ) (c t : ℝ) :
    LSeries.term mangoldt (c+t*I) n =
      LSeries.term mangoldt c n * exp (-I*t*Real.log n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_def₀ (by simp [mangoldt]), LSeries.term_def₀ (by simp [mangoldt]),
    mul_assoc, cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn),
    cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), ← Complex.exp_add, natCast_log]
  congr 2
  ring

private theorem tilt_cancel (n : ℕ) (c : ℝ) :
    LSeries.term mangoldt c n * exp (((c:ℂ)-1/2)*Real.log n) =
      ((vonMangoldt n / Real.sqrt n : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_def₀ (by simp [mangoldt]), cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn),
    mul_assoc, ← Complex.exp_add, natCast_log, ofReal_div, div_eq_mul_inv]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)),
    ofReal_exp, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

private theorem phase_norm (t y : ℝ) : ‖exp (-I*t*y)‖ = 1 := by simp [norm_exp, mul_re]

private theorem tsum_neg_logDeriv {c : ℝ} (hc : 1 < c) (t : ℝ) :
    (∑' n, LSeries.term mangoldt (c+t*I) n) = -logDeriv riemannZeta (c+t*I) := by
  simpa [LSeries, mangoldt, logDeriv_apply, neg_div] using
    LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := (c:ℂ)+t*I) (by simpa)

/-- On each line Re s > 1 the Dirichlet series bounds the logarithmic derivative uniformly. -/
theorem bounded_logDeriv_zeta_line {c : ℝ} (hc : 1 < c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, ‖logDeriv riemannZeta (c+t*I)‖ ≤ B := by
  have hm : Summable (LSeries.term mangoldt (c:ℂ)) := LSeriesSummable_vonMangoldt (by simpa)
  refine ⟨∑' n, ‖LSeries.term mangoldt c n‖, tsum_nonneg fun _ ↦ norm_nonneg _, fun t ↦ ?_⟩
  rw [← norm_neg, ← tsum_neg_logDeriv hc]
  have h (n : ℕ) : ‖LSeries.term mangoldt (c+t*I) n‖ = ‖LSeries.term mangoldt c n‖ := by
    rw [term_on_line, norm_mul, phase_norm, mul_one]
  simpa only [h] using norm_tsum_le_tsum_norm (hm.norm.congr fun n ↦ (h n).symm)

/-- Integration against the negative logarithmic derivative selects the positive prime arguments. -/
theorem prime_integral_hasSum {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hs : HasCompactSupport k)
    {c : ℝ} (hc : 1 < c) :
    HasSum (fun n : ℕ ↦ ((vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n))
      ((2*(π:ℂ))⁻¹ * ∫ t : ℝ, weight k (c+t*I) * (-logDeriv riemannZeta (c+t*I))) := by
  let W (t : ℝ) := weight k (c+t*I)
  let F (n : ℕ) (t : ℝ) := LSeries.term mangoldt (c+t*I) n * W t
  have hW : Integrable W := integrable_weight_line hk hs c
  have hFn (n : ℕ) (t : ℝ) : ‖F n t‖ = ‖LSeries.term mangoldt c n‖ * ‖W t‖ := by
    simp only [F, term_on_line, norm_mul, phase_norm, mul_one]
  have hFi (n : ℕ) : Integrable (F n) := by
    apply (hW.norm.const_mul ‖LSeries.term mangoldt c n‖).mono' _ (.of_forall fun t ↦ (hFn n t).le)
    simp only [F, term_on_line]
    exact ((continuous_const.mul (by fun_prop)).mul
      ((differentiable_weight hk.continuous hs).continuous.comp (by fun_prop))).aestronglyMeasurable
  have hm : Summable (LSeries.term mangoldt (c:ℂ)) := LSeriesSummable_vonMangoldt (by simpa)
  have hsum := hasSum_integral_of_summable_integral_norm hFi (by
    simp_rw [hFn, integral_const_mul]
    exact hm.norm.mul_right _)
  have he (t : ℝ) : (∑' n, F n t) = W t * (-logDeriv riemannZeta (c+t*I)) := by
    change (∑' n, LSeries.term mangoldt (c+t*I) n * W t) = _
    rw [tsum_mul_right, tsum_neg_logDeriv hc, mul_comm]
  simp_rw [he] at hsum
  apply ((hsum.mul_left (2*(π:ℂ))⁻¹).congr_fun fun n ↦ ?_)
  simp only [F, term_on_line, mul_assoc (LSeries.term mangoldt _ n), integral_const_mul]
  rw [show (fun t : ℝ ↦ exp (-I*t*Real.log n)*W t) =
    (fun t : ℝ ↦ W t*exp (-I*t*Real.log n)) by funext; ring]
  change _ = _ * (_ * ∫ t : ℝ, weight k (c+t*I)*exp (-I*t*Real.log n))
  rw [weight_inversion hk hs]
  rw [← tilt_cancel n c, ofReal_mul, ofReal_ofNat]
  field_simp [Real.pi_ne_zero]

/-- The even part of a test supplies both prime arguments in Weil's formula. -/
theorem prime_integral_eq {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hs : HasCompactSupport k)
    {c : ℝ} (hc : 1 < c) :
    (2*(π:ℂ))⁻¹ * (∫ t : ℝ, (weight k (c+t*I) + weight k (1-(c+t*I))) *
      (-logDeriv riemannZeta (c+t*I))) =
        ∑' n : ℕ, ((vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) := by
  let k' (u : ℝ) := k (-u)
  have hk' : ContDiff ℝ 2 k' := hk.comp contDiff_id.neg
  have hs' : HasCompactSupport k' := hs.comp_homeomorph (Homeomorph.neg ℝ)
  have hw (s : ℂ) : weight (k+k') s = weight k s + weight k (1-s) := by
    rw [weight_one_sub]
    simp only [weight, transform, Pi.add_apply, add_mul]
    exact integral_add (transform_integrable hk.continuous hs _)
      (transform_integrable hk'.continuous hs' _)
  have h := (prime_integral_hasSum (k := k+k') (hk.add hk') (hs.add hs') hc).tsum_eq.symm
  simp_rw [hw] at h
  exact h

end WeilExplicit
