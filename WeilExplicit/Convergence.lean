import WeilExplicit.Transform
import WeilExplicit.ZeroSum
import WeilExplicit.DigammaSeries

/-! # Absolute convergence of the spectral and archimedean terms -/

namespace WeilExplicit

open WeilExplicit (transform)

open Complex Real MeasureTheory Set

/-- The zero series of the explicit formula converges absolutely. -/
theorem summable_zero_transform {k : ℝ → ℂ} (hc : ContDiff ℝ 2 k) (hk : HasCompactSupport k) :
    Summable fun ρ : stripZeros ↦ (zeroMult ρ : ℂ) * transform k (((ρ : ℂ) - 1/2)/I) := by
  obtain ⟨M, _, hM⟩ := transform_decay hc hk (1/2)
  apply Summable.of_norm_bounded (summable_zeroMult_div_one_add_normSq.mul_right M)
  intro ρ
  have hz : |(((ρ : ℂ)-1/2)/I).im| ≤ 1/2 := by
    simp [div_I]
    exact abs_le.mpr ⟨by linarith [ρ.property.2.2], by linarith [ρ.property.2.1]⟩
  rw [norm_mul, Complex.norm_natCast, div_mul_eq_mul_div, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (hM _ hz) (Nat.cast_nonneg _)

/-- Digamma on the strip used to move the Gamma integral. -/
theorem norm_digamma_half_le {s : ℂ} (ha : 1/2 ≤ s.re) (hb : s.re ≤ 2) :
    ‖digamma (s/2)‖ ≤ 30 * √(1 + |s.im|) := by
  have hre : (s/2).re = s.re/2 := by simp
  have him : (s/2).im = s.im/2 := by simp
  apply (norm_digamma_le (by rw [hre]; linarith)).trans
  have hn : ‖s/2 - 1‖ + 2 ≤ 4 * (1+|s.im|) := by
    have h := norm_le_abs_re_add_abs_im (s/2-1)
    rw [sub_re, hre, one_re, abs_of_nonpos (by linarith), sub_im, one_im, sub_zero,
      him, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)] at h
    linarith [abs_nonneg s.im]
  have hl := (Real.log_le_log (by positivity) hn).trans
    (Real.log_le_rpow_div (by positivity) (by norm_num : (0:ℝ) < 1/2))
  rw [← sqrt_eq_rpow, sqrt_mul (by norm_num), show √(4:ℝ) = 2 by
    rw [show (4:ℝ) = 2^2 by norm_num, sqrt_sq (by norm_num)]] at hl
  have h1 : 1 ≤ √(1 + |s.im|) := Real.one_le_sqrt.mpr (by linarith [abs_nonneg s.im])
  linarith

/-- Integrability of the archimedean integrand, with the real part of digamma. -/
theorem integrable_archimedean {k : ℝ → ℂ} (hc : ContDiff ℝ 2 k) (hk : HasCompactSupport k) :
    Integrable (fun r : ℝ ↦ transform k r *
      (((digamma (1/4 + I*r/2)).re - Real.log π : ℝ) : ℂ)) := by
  obtain ⟨M, hM, hdec⟩ := transform_decay hc hk 0
  have hψ (r : ℝ) : 0 < (1/4 + I*(r : ℂ)/2).re := by norm_num
  have ht := (differentiable_transform hc.continuous hk).continuous
  apply integrable_of_quadratic_decay (M := M*(30 + |Real.log π|)) (by positivity)
  · apply (ht.comp continuous_ofReal).mul
    apply continuous_ofReal.comp
    apply Continuous.sub _ continuous_const
    apply continuous_re.comp
    exact continuous_iff_continuousAt.mpr fun r ↦
      (analyticAt_digamma (hψ r)).continuousAt.comp (f := fun r : ℝ ↦ 1/4+I*(r : ℂ)/2) (by fun_prop)
  intro r
  have hz := norm_digamma_half_le (s := 1/2 + I*(r : ℂ)) (by norm_num) (by norm_num)
  rw [add_div] at hz
  norm_num at hz
  have hdec' := hdec (r : ℂ) (by simp)
  simp only [normSq_ofReal, ← sq] at hdec'
  have h1 : 1 ≤ √(1+|r|) := Real.one_le_sqrt.mpr (by linarith [abs_nonneg r])
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ ‖transform k r‖ * (‖digamma (1/4 + I*(r : ℂ)/2)‖ + |Real.log π|) := by
      gcongr
      exact (abs_sub _ _).trans (add_le_add (abs_re_le_norm _) le_rfl)
    _ ≤ (M/(1+r^2)) * (30*√(1+|r|) + |Real.log π| *√(1+|r|)) := by
      gcongr
      exact le_mul_of_one_le_right (abs_nonneg _) h1
    _ = _ := by ring

end WeilExplicit
