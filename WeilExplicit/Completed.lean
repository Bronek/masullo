import WeilExplicit.Zeros
import Mathlib.Analysis.Calculus.LogDeriv

/-! # Removing the two poles of the completed zeta function -/

namespace WeilExplicit

open Complex Filter
open scoped Topology

/-- Twice Riemann's xi function, with the removable values supplied by the entire part. -/
protected noncomputable def xi (s : ℂ) : ℂ := s*(s-1)*completedRiemannZeta₀ s + 1

open WeilExplicit (xi)

/-- Riemann’s pole-removed completion is entire. -/
theorem differentiable_xi : Differentiable ℂ xi :=
  ((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1

/-- Removing the simple pole of completed zeta at one gives the value one. -/
@[simp] theorem xi_one : xi 1 = 1 := by simp [xi]

/-- Xi takes equal values at s and 1−s. -/
theorem xi_one_sub (s : ℂ) : xi (1-s) = xi s := by
  simp only [xi, completedRiemannZeta₀_one_sub]
  ring

/-- Away from both poles, xi is completed zeta multiplied by s(s−1). -/
theorem xi_eq_completed {s : ℂ} (h₀ : s ≠ 0) (h₁ : s ≠ 1) :
    xi s = s*(s-1)*completedRiemannZeta s := by
  rw [xi, completedRiemannZeta_eq]
  field_simp [h₀, sub_ne_zero.mpr h₁.symm]
  ring

/-- At positive real part, multiplying zeta by its real-place Gamma factor gives completed zeta. -/
theorem completed_eq_gamma_mul {s : ℂ} (h : 0 < s.re) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have hn : s ≠ 0 := fun e ↦ by simp [e] at h
  rw [riemannZeta_def_of_ne_zero hn]
  field_simp [Gammaℝ_ne_zero_of_re_pos h]

private theorem xi_nonzero_right {s : ℂ} (hs : 1 ≤ s.re) : xi s ≠ 0 := by
  by_cases h₁ : s = 1
  · simp [h₁]
  have h : 0 < s.re := lt_of_lt_of_le zero_lt_one hs
  have h₀ : s ≠ 0 := fun e ↦ by simp [e] at h
  rw [xi_eq_completed h₀ h₁, completed_eq_gamma_mul h]
  exact mul_ne_zero (mul_ne_zero h₀ (sub_ne_zero.mpr h₁))
    (mul_ne_zero (Gammaℝ_ne_zero_of_re_pos h) (riemannZeta_ne_zero_of_one_le_re hs))

/-- The zeros of xi are precisely the zeta zeros in the open critical strip. -/
theorem xi_eq_zero_iff {s : ℂ} : xi s = 0 ↔ s ∈ stripZeros := by
  by_cases hs : 0 < s.re
  · by_cases ht : s.re < 1
    · have h₀ : s ≠ 0 := fun e ↦ by simp [e] at hs
      have h₁ : s ≠ 1 := fun e ↦ by simp [e] at ht
      simp [xi_eq_completed h₀ h₁, completed_eq_gamma_mul hs, stripZeros, hs, ht,
        h₀, sub_ne_zero.mpr h₁, Gammaℝ_ne_zero_of_re_pos hs]
    · simp [xi_nonzero_right (le_of_not_gt ht), stripZeros, ht]
  · have h : 1 ≤ (1-s).re := by simp; linarith
    rw [← xi_one_sub s]
    simp [xi_nonzero_right h, stripZeros, hs]

private theorem xi_order_eq_completed {s : ℂ} (h₀ : s ≠ 0) (h₁ : s ≠ 1) :
    analyticOrderAt xi s = analyticOrderAt completedRiemannZeta s := by
  have he : xi =ᶠ[𝓝 s] (fun z ↦ z*(z-1)) * completedRiemannZeta :=
    (eventually_ne_nhds h₀).and (eventually_ne_nhds h₁) |>.mono fun _ h ↦ xi_eq_completed h.1 h.2
  have hp : AnalyticAt ℂ (fun z : ℂ ↦ z*(z-1)) s := by fun_prop
  have hL := analyticAt_completedZeta h₀ h₁
  rw [analyticOrderAt_congr he, analyticOrderAt_mul hp hL,
    hp.analyticOrderAt_eq_zero.mpr (mul_ne_zero h₀ (sub_ne_zero.mpr h₁)), zero_add]

/-- At a strip zero, xi and zeta have the same analytic order. -/
theorem xi_order_eq {s : ℂ} (hs : s ∈ stripZeros) :
    analyticOrderAt xi s = analyticOrderAt riemannZeta s :=
  (xi_order_eq_completed (fun h ↦ by simpa [h] using hs.2.1)
    (fun h ↦ by simpa [h] using hs.2.2)).trans (zeta_order_eq_completed hs.2.1 hs.2.2).symm

/-- The two poles each subtract a simple fraction from the logarithmic derivative of xi. -/
theorem logDeriv_completed_eq_xi {s : ℂ} (h₀ : s ≠ 0) (h₁ : s ≠ 1) (hn : xi s ≠ 0) :
    logDeriv completedRiemannZeta s = logDeriv xi s - (s-1)⁻¹ - s⁻¹ := by
  have he : xi =ᶠ[𝓝 s] (fun z ↦ (z*(z-1)) * completedRiemannZeta z) :=
    (eventually_ne_nhds h₀).and (eventually_ne_nhds h₁) |>.mono fun _ h ↦ xi_eq_completed h.1 h.2
  have hL : completedRiemannZeta s ≠ 0 := fun e ↦ hn (by rw [xi_eq_completed h₀ h₁, e, mul_zero])
  have h1 := logDeriv_mul (f := fun z : ℂ ↦ z*(z-1)) (g := completedRiemannZeta)
      s (mul_ne_zero h₀ (sub_ne_zero.mpr h₁)) hL
    (by fun_prop) (differentiableAt_completedZeta h₀ h₁)
  have h2 := logDeriv_mul (f := fun z : ℂ ↦ z) (g := fun z : ℂ ↦ z-1) s h₀ (sub_ne_zero.mpr h₁)
      differentiableAt_id (differentiableAt_id.sub_const 1)
  simp only [Pi.mul_def] at h1 h2
  rw [(logDeriv_congr_nhds he).self_of_nhds, h1, h2]
  simp [logDeriv_apply, one_div]
  ring

/-- The logarithmic derivative of completed zeta changes sign under s ↦ 1−s. -/
theorem logDeriv_completed_one_sub {s : ℂ} (h₀ : s ≠ 0) (h₁ : s ≠ 1) :
    logDeriv completedRiemannZeta (1-s) = -logDeriv completedRiemannZeta s := by
  have h := logDeriv_comp (f := completedRiemannZeta) (g := fun z ↦ 1-z)
    (x := s) (differentiableAt_completedZeta (sub_ne_zero.mpr h₁.symm) (by simpa)) (by fun_prop)
  simp [Function.comp_def, completedRiemannZeta_one_sub] at h
  rw [h, neg_neg]

end WeilExplicit
