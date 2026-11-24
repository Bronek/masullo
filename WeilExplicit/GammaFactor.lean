import WeilExplicit.LogDerivative
import WeilExplicit.Convergence
import WeilExplicit.Completed

/-! # Logarithmic derivative of the real-place Gamma factor -/

namespace WeilExplicit

open Complex Real Filter
open scoped Topology ComplexConjugate

/-- The real-place Gamma factor is holomorphic in the open right half-plane. -/
theorem analyticAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gammaℝ s := by
  convert! (differentiable_Gammaℝ_inv.analyticAt s).inv
    (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hs)) using 1
  ext z
  simp

/-- The real-place Gamma logarithmic derivative is (ψ(s/2) − log π)/2 on Re s > 0. -/
theorem logDeriv_gamma_factor {s : ℂ} (hs : 0 < s.re) :
    logDeriv Gammaℝ s = (digamma (s/2) - Real.log π)/2 := by
  let e (z : ℂ) := log (π : ℂ) * (-z/2)
  have he : Gammaℝ = fun z ↦ exp (e z) * Complex.Gamma (z/2) := by
    funext z
    rw [Gammaℝ_def, cpow_def_of_ne_zero (ofReal_ne_zero.mpr pi_ne_zero)]
  have hp : 0 < (s/2).re := by simpa using half_pos hs
  have hd := Complex.differentiableAt_Gamma (s/2) fun n h ↦ by simp [h] at hp; linarith
  have de : HasDerivAt e (Complex.log (π:ℂ)*(-1/2)) s := by
    simpa [e] using (((hasDerivAt_id s).neg.div_const 2).const_mul (Complex.log (π:ℂ)))
  rw [he, logDeriv_mul (f := fun z ↦ exp (e z))
      (g := fun z ↦ Complex.Gamma (z/2)) s (Complex.exp_ne_zero _) (Gamma_ne_zero_of_re_pos hp)
    de.cexp.differentiableAt (hd.comp s (differentiableAt_id.div_const 2))]
  change logDeriv (Complex.exp ∘ e) s + logDeriv (Complex.Gamma ∘ (fun z : ℂ ↦ z/2)) s = _
  rw [logDeriv_comp Complex.differentiableAt_exp de.differentiableAt, Complex.logDeriv_exp,
    logDeriv_comp (g := fun z : ℂ ↦ z/2) (x := s) hd (differentiableAt_id.div_const _),
      de.deriv, ← Complex.ofReal_log pi_pos.le]
  simp [digamma, logDeriv_apply]
  ring

/-- Where zeta is regular and nonzero on Re s > 0, its Gamma factor contributes additively. -/
theorem logDeriv_completed_split {s : ℂ} (hs : 0 < s.re) (h₁ : s ≠ 1) (hn : riemannZeta s ≠ 0) :
    logDeriv completedRiemannZeta s = logDeriv Gammaℝ s + logDeriv riemannZeta s := by
  have he : completedRiemannZeta =ᶠ[𝓝 s] fun z ↦ Gammaℝ z * riemannZeta z := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    exact completed_eq_gamma_mul hz
  rw [(logDeriv_congr_nhds he).self_of_nhds, logDeriv_mul s (Gammaℝ_ne_zero_of_re_pos hs) hn
    (analyticAt_Gammaℝ hs).differentiableAt (differentiableAt_riemannZeta h₁)]

/-- Summing the reflected Gamma derivatives on the critical line leaves the real digamma part. -/
protected theorem gamma_pair (t : ℝ) :
    logDeriv Gammaℝ (1/2+t*I) + logDeriv Gammaℝ (1/2-t*I) =
      (((digamma (1/4+I*t/2)).re - Real.log π : ℝ) : ℂ) := by
  rw [logDeriv_gamma_factor (by norm_num), logDeriv_gamma_factor (by norm_num)]
  have e : ((1/2:ℂ)+t*I)/2 = 1/4 + I*t/2 := by ring
  have e' : ((1/2:ℂ)-t*I)/2 = conj (1/4 + I*t/2) := by
    rw [← e]
    simp only [map_div₀, map_add, map_one, map_mul, conj_ofReal, conj_I, map_ofNat]
    ring
  rw [e, e', show ∀ z, digamma (conj z) = conj (digamma z) from logDeriv_conj Complex.Gamma_conj,
    ofReal_sub]
  have h := add_conj (digamma (1/4+I*t/2))
  push_cast at h
  linear_combination h/2

end WeilExplicit
