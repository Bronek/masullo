import WeilExplicit.Transform
import Mathlib.Analysis.Fourier.Inversion

/-! # Angular Fourier inversion on shifted vertical lines -/

namespace WeilExplicit

open WeilExplicit (transform)

open Complex MeasureTheory Real
open scoped FourierTransform

/-- The transform in the zeta variable, with angular frequency (s−1/2)/i. -/
protected noncomputable def weight (k : ℝ → ℂ) (s : ℂ) := transform k ((s-1/2)/I)

open WeilExplicit (weight)

/-- The affine change from frequency to the zeta variable preserves entire differentiability. -/
theorem differentiable_weight {k : ℝ → ℂ} (hc : Continuous k) (hk : HasCompactSupport k) :
    Differentiable ℂ (weight k) :=
  (differentiable_transform hc hk).comp (by fun_prop)

/-- On a vertical line the weight is the angular transform of an exponentially tilted test. -/
theorem weight_on_line (k : ℝ → ℂ) (c t : ℝ) :
    weight k (c+t*I) =
      transform (fun u ↦ k u * exp (((c:ℂ)-1/2)*u)) t := by
  unfold weight transform
  apply integral_congr_ae
  filter_upwards with u
  rw [mul_assoc (k u), ← Complex.exp_add]
  congr 2
  field_simp
  ring

/-- Two derivatives of a compactly supported test give an integrable transform on the real axis. -/
theorem integrable_transform_real {k : ℝ → ℂ} (hc : ContDiff ℝ 2 k) (hk : HasCompactSupport k) :
    Integrable (fun t : ℝ ↦ transform k t) := by
  obtain ⟨M, hM, hb⟩ := transform_decay hc hk 0
  apply integrable_of_quadratic_decay hM
    ((differentiable_transform hc.continuous hk).continuous.comp
    continuous_ofReal)
  intro r
  have h := hb (r : ℂ) (by simp)
  simp only [normSq_ofReal, ← sq] at h
  apply h.trans
  gcongr
  exact le_mul_of_one_le_right hM (Real.one_le_sqrt.mpr (by linarith [abs_nonneg r]))

/-- Mathlib’s Fourier frequency w corresponds to angular frequency −2πw. -/
theorem fourier_eq_transform (k : ℝ → ℂ) (w : ℝ) :
    𝓕 k w = transform k ((-2*π*w : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, transform]
  apply integral_congr_ae
  filter_upwards with u
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

/-- Pointwise inversion with the positive exponential convention and Lebesgue measure. -/
theorem transform_inversion {k : ℝ → ℂ} (hc : ContDiff ℝ 2 k) (hk : HasCompactSupport k) (y : ℝ) :
    (∫ t : ℝ, transform k t * exp (-I*t*y)) = (2*π : ℝ) * k y := by
  have hf : Integrable (𝓕 k) := by
    simp_rw [funext (fourier_eq_transform k)]
    exact (integrable_transform_real hc hk).comp_mul_left' (by positivity)
  have h := (hc.continuous.integrable_of_hasCompactSupport hk).fourier_fourierInv_eq hf
    (hc.continuous.continuousAt (x := y))
  rw [Real.fourier_real_eq_integral_exp_smul] at h
  let f (t : ℝ) := transform k t * exp (-I*t*y)
  have he (v : ℝ) : exp ((↑(-2*π*v*y) : ℂ)*I) • (𝓕⁻ k v) = f (2*π*v) := by
    rw [Real.fourierInv_eq_fourier_neg, fourier_eq_transform, smul_eq_mul, mul_comm]
    dsimp [f]
    rw [show -2*π*(-v) = 2*π*v by ring]
    congr 2
    push_cast
    ring
  simp_rw [he] at h
  rw [Measure.integral_comp_mul_left, abs_of_pos (by positivity), Complex.real_smul] at h
  change (∫ t, f t) = _
  rw [← h, ← mul_assoc, ← ofReal_mul, mul_inv_cancel₀ (by positivity), ofReal_one, one_mul]

/-- Absolute convergence of the line transform. -/
theorem integrable_weight_line {k : ℝ → ℂ} (hc : ContDiff ℝ 2 k) (hk : HasCompactSupport k)
    (c : ℝ) : Integrable (fun t : ℝ ↦ weight k (c+t*I)) := by
  simp_rw [weight_on_line]
  exact integrable_transform_real (hc.mul ((contDiff_const.mul ofRealCLM.contDiff).cexp))
    hk.mul_right

/-- Fourier inversion on a vertical line, at any real evaluation point. -/
theorem weight_inversion {k : ℝ → ℂ} (hc : ContDiff ℝ 2 k) (hk : HasCompactSupport k) (c y : ℝ) :
    (∫ t : ℝ, weight k (c+t*I) * exp (-I*t*y)) =
      (2*π : ℝ) * (k y * exp (((c:ℂ)-1/2)*y)) := by
  simp_rw [weight_on_line]
  exact transform_inversion (hc.mul ((contDiff_const.mul ofRealCLM.contDiff).cexp)) hk.mul_right y

/-- Reflection about the center of the strip acts on tests by reflection of the real variable. -/
theorem weight_one_sub (k : ℝ → ℂ) (s : ℂ) :
    weight k (1-s) = weight (fun u ↦ k (-u)) s := by
  unfold weight transform
  rw [← integral_neg_eq_self (fun u : ℝ ↦ k u * exp (I * ((1-s-1/2)/I) * u))]
  apply integral_congr_ae
  filter_upwards with u
  congr 2
  push_cast
  ring

end WeilExplicit
