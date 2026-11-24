import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # The Fourier–Laplace transform of a compactly supported test function -/

namespace WeilExplicit

open Complex MeasureTheory Metric
open scoped Topology

/-- The transform with positive exponential and angular frequency. -/
protected noncomputable def transform (k : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, k u * exp (I * z * u)

open WeilExplicit (transform)

/-- The transform integrand of a continuous compactly supported function is integrable. -/
theorem transform_integrable {k : ℝ → ℂ} (hc : Continuous k) (hk : HasCompactSupport k) (z : ℂ) :
    Integrable (fun u : ℝ ↦ k u * exp (I * z * u)) :=
  (hc.mul (by fun_prop)).integrable_of_hasCompactSupport hk.mul_right

private theorem norm_kernel_le {z : ℂ} {u D B : ℝ} (hz : |z.im| ≤ D) (hu : |u| ≤ B) :
    ‖exp (I * z * u)‖ ≤ Real.exp (D * B) := by
  rw [norm_exp, Real.exp_le_exp]
  simp [mul_re]
  calc
    -(z.im * u) ≤ |-(z.im * u)| := le_abs_self _
    _ ≤ D * B := by
      rw [abs_neg, abs_mul]
      exact mul_le_mul hz hu (abs_nonneg _) ((abs_nonneg _).trans hz)

/-- The Fourier–Laplace transform of a continuous compactly supported function is entire. -/
theorem differentiable_transform {k : ℝ → ℂ} (hc : Continuous k) (hk : HasCompactSupport k) :
    Differentiable ℂ (transform k) := by
  obtain ⟨B, hBpos, hB⟩ := hk.exists_pos_le_norm
  intro z
  let F (w : ℂ) (u : ℝ) := k u * exp (I * w * u)
  let F' (w : ℂ) (u : ℝ) := F w u * (I * u)
  have hd (u : ℝ) (w : ℂ) : HasDerivAt (F · u) (F' w u) w := by
    simpa [F, F', mul_assoc] using
      (((((hasDerivAt_id w).const_mul I).mul_const (u : ℂ)).cexp).const_mul (k u))
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
    (bound := fun u ↦ ‖k u‖ * Real.exp ((‖z‖+1)*B) * B) (ball_mem_nhds z zero_lt_one)
    (.of_forall fun w ↦ (transform_integrable hc hk w).aestronglyMeasurable)
    (transform_integrable hc hk z) (Continuous.aestronglyMeasurable (by dsimp [F', F]; fun_prop)) ?_
    (((hc.integrable_of_hasCompactSupport hk).norm.mul_const _).mul_const _)
    (.of_forall fun u w _ ↦ hd u w)).2.differentiableAt
  filter_upwards with u w
  intro hw
  by_cases hu : ‖u‖ ≤ B
  · have hw' : |w.im| ≤ ‖z‖ + 1 := by
      have := norm_sub_norm_le w z
      linarith [abs_im_le_norm w, mem_ball_iff_norm.mp hw]
    simp only [F', F, norm_mul, norm_I, one_mul, norm_real]
    gcongr
    exact norm_kernel_le hw' hu
  · simp [F', F, hB u (le_of_not_ge hu)]

/-- A continuous compactly supported test has a bounded transform on every horizontal strip. -/
theorem exists_transform_bound {k : ℝ → ℂ} (hc : Continuous k) (hk : HasCompactSupport k) (D : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, |z.im| ≤ D → ‖transform k z‖ ≤ M := by
  obtain ⟨B, _, hB⟩ := hk.exists_pos_le_norm
  refine ⟨_, integral_nonneg (μ := volume) (f := fun u ↦ ‖k u‖ * Real.exp (D*B))
    (fun u ↦ by positivity), fun z hz ↦ ?_⟩
  apply norm_integral_le_of_norm_le ((hc.integrable_of_hasCompactSupport hk).norm.mul_const _)
  filter_upwards with u
  by_cases hu : ‖u‖ ≤ B
  · rw [norm_mul]; gcongr; exact norm_kernel_le hz hu
  · simp [hB u (le_of_not_ge hu)]

/-- One integration by parts moves a derivative from the test function to the exponential. -/
theorem transform_deriv {k : ℝ → ℂ} (hc : ContDiff ℝ 1 k) (hk : HasCompactSupport k) (z : ℂ) :
    transform (deriv k) z = -(I * z) * transform k z := by
  let v (u : ℝ) := exp (I * z * u)
  have hv (u : ℝ) : HasDerivAt v (v u * (I*z)) u := by
    apply HasDerivAt.comp_ofReal (e := fun w ↦ exp (I*z*w))
    simpa [v] using (((hasDerivAt_id (u : ℂ)).const_mul (I*z)).cexp)
  have hk' := transform_integrable (hc.continuous_deriv le_rfl) hk.deriv z
  have hkv := transform_integrable hc.continuous hk z
  have hi : Integrable (fun u : ℝ ↦ k u * (v u * (I*z))) := by
    simpa [v, mul_assoc] using hkv.mul_const (I*z)
  have H := integral_mul_deriv_eq_deriv_mul_of_integrable (u := k) (v := v)
    (fun x _ ↦ (hc.differentiable one_ne_zero x).hasDerivAt) (fun x _ ↦ hv x) hi hk' hkv
  simp only [← mul_assoc, integral_mul_const] at H
  change transform k z * I * z = -transform (deriv k) z at H
  linear_combination H

/-- Two integrations by parts give uniform quadratic decay on every horizontal strip. -/
theorem transform_decay {k : ℝ → ℂ} (hc : ContDiff ℝ 2 k) (hk : HasCompactSupport k) (D : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, |z.im| ≤ D → ‖transform k z‖ ≤ M / (1 + normSq z) := by
  have hc' : ContDiff ℝ 1 (deriv k) := (contDiff_succ_iff_deriv.mp hc).2.2
  obtain ⟨A, hA, h₀⟩ := exists_transform_bound hc.continuous hk D
  obtain ⟨B, hB, h₂⟩ := exists_transform_bound (hc'.continuous_deriv le_rfl) hk.deriv.deriv D
  refine ⟨A+B, add_nonneg hA hB, fun z hz ↦ ?_⟩
  have h := h₂ z hz
  rw [transform_deriv hc' hk.deriv, transform_deriv (hc.of_le (by decide)) hk] at h
  simp only [norm_mul, norm_neg, norm_I, one_mul] at h
  rw [le_div_iff₀ (add_pos_of_pos_of_nonneg zero_lt_one (normSq_nonneg _)), normSq_eq_norm_sq]
  nlinarith only [h, h₀ z hz]

open Real in
/-- A continuous function bounded in norm by M√(1+|r|)/(1+r²) is integrable. -/
theorem integrable_of_quadratic_decay {f : ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hf : Continuous f) (hb : ∀ r : ℝ, ‖f r‖ ≤ M * √(1+|r|) / (1+r^2)) : Integrable f := by
  have hi := integrable_one_add_norm (μ := volume) (E := ℝ) (r := 3/2) (by norm_num)
  apply (hi.const_mul (2*M)).mono' hf.aestronglyMeasurable (.of_forall fun r ↦ (hb r).trans ?_)
  rw [Real.norm_eq_abs, show -(3/2 : ℝ) = 1/2 - 2 by ring, Real.rpow_sub (by positivity),
    Real.rpow_two, ← sqrt_eq_rpow, ← mul_div_assoc]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h := sq_nonneg (|r|-1)
  have hh : (1+|r|)^2 ≤ 2*(1+r^2) := by nlinarith [sq_abs r]
  nlinarith only [mul_le_mul_of_nonneg_left hh (show 0 ≤ M * √(1+|r|) by positivity)]

end WeilExplicit
