import WeilExplicit.LineBounds
import WeilExplicit.RectangleLimit

/-! # Shifting the Gamma integral to the critical line -/

namespace WeilExplicit

open WeilExplicit (transform weight)

open Complex Real MeasureTheory Set Filter
open scoped Topology

/-- Quadratic weight decay gives integrability of the Gamma term on lines with 1/2 ≤ Re s ≤ 2. -/
theorem integrable_gamma_line {W : ℂ → ℂ} (hw : Continuous W) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖W z‖ ≤ M/(1+z.im^2))
    {x : ℝ} (hx : 1/2 ≤ x) (hx' : x ≤ 2) :
    Integrable (fun t : ℝ ↦ W (x+t*I) * logDeriv Gammaℝ (x+t*I)) := by
  obtain ⟨A,hA,ha⟩ := gamma_strip_bound
  apply integrable_line_mul (M := M) (A := A) hM hA hw
  · intro t
    exact (analyticAt_logDeriv_gamma (by simp; linarith : 0 < ((x:ℂ)+t*I).re)).continuousAt
  · intro t
    simpa using h (x+t*I) (by simp; linarith) (by simpa using hx')
  · intro t
    simpa using ha (x+t*I) (by simpa using hx) (by simpa using hx')

/-- Shifting the Gamma integral from Re s = 2 to Re s = 1/2 preserves its value. -/
theorem shift_gamma_line {W : ℂ → ℂ} (hw : Differentiable ℂ W) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖W z‖ ≤ M/(1+z.im^2)) :
    (∫ t : ℝ, W (2+t*I) * logDeriv Gammaℝ (2+t*I)) =
      ∫ t : ℝ, W (1/2+t*I) * logDeriv Gammaℝ (1/2+t*I) := by
  let f (s : ℂ) := W s * logDeriv Gammaℝ s
  obtain ⟨A,hA,ha⟩ := gamma_strip_bound
  have hlim := rectIntegral_tendsto (f := f) (a := 1/2) (b := 2) tendsto_natCast_atTop_atTop
    (integrable_gamma_line hw.continuous hM h (by norm_num) (by norm_num))
    (integrable_gamma_line hw.continuous hM h (by norm_num) (by norm_num)) (B := M*(2*A)) (by
      filter_upwards [eventually_ge_atTop 1] with j hj
      intro z hz ht
      rw [uIcc_of_le (by norm_num)] at hz
      have hj' : (1:ℝ) ≤ j := by exact_mod_cast hj
      have hb := ha z hz.1 hz.2
      rw [ht] at hb
      apply WeilExplicit.horizontal_product_bound hM (by linarith)
      · simpa [← ht, sq_abs] using h z (by linarith [hz.1]) hz.2
      · nlinarith [mul_le_mul_of_nonneg_left (WeilExplicit.sqrt_one_add_le_two_mul hj') hA])
  have hz (j : ℕ) : rectIntegral f (1/2) 2 (-(j:ℝ)) j = 0 := by
    apply rectIntegral_eq_zero
    intro z hz
    have hp := hz.1
    rw [uIcc_of_le (by norm_num)] at hp
    exact DifferentiableAt.differentiableWithinAt <|
      (hw z).mul (analyticAt_logDeriv_gamma (by linarith [hp.1])).differentiableAt
  simp_rw [hz] at hlim
  have he := tendsto_nhds_unique hlim tendsto_const_nhds
  simpa [f, sub_eq_zero, I_ne_zero] using he

/-- On the critical line the argument of the Fourier transform is the real height. -/
@[simp] theorem weight_critical (k : ℝ → ℂ) (t : ℝ) : weight k (1/2+t*I) = transform k t := by
  simp [weight]

/-- Summing the two reflected terms replaces the Gamma logarithmic derivative by a real part. -/
theorem gamma_integral_eq {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hs : HasCompactSupport k) :
    (∫ t : ℝ, pairedWeight k (2+t*I) * logDeriv Gammaℝ (2+t*I)) =
      ∫ t : ℝ, transform k t * (((digamma (1/4+I*t/2)).re - Real.log π : ℝ) : ℂ) := by
  obtain ⟨M,hM,hm⟩ := pairedWeight_strip_decay hk hs
  rw [shift_gamma_line (differentiable_pairedWeight hk.continuous hs) hM hm]
  let G (t : ℝ) := logDeriv Gammaℝ (1/2+t*I)
  let F (t : ℝ) := transform k t
  have hr (t : ℝ) : 1-(1/2+(t:ℂ)*I) = 1/2+(-t:ℝ)*I := by push_cast; ring
  obtain ⟨N,hN,hn⟩ := weight_strip_decay hk hs
  have hi : Integrable (fun t : ℝ ↦ F t * G t) := by
    simpa only [F,G, ofReal_div, ofReal_one, ofReal_ofNat, weight_critical]
      using integrable_gamma_line (differentiable_weight hk.continuous hs).continuous
        hN hn (x := 1/2) le_rfl (by norm_num)
  obtain ⟨N',hN',hn'⟩ := reflected_weight_strip_decay hk hs
  have hi' : Integrable (fun t : ℝ ↦ F (-t) * G t) := by
    simpa only [F,G, ofReal_div, ofReal_one, ofReal_ofNat, hr, weight_critical]
      using integrable_gamma_line (W := fun z ↦ weight k (1-z))
        (((differentiable_weight hk.continuous hs).comp (f := fun z : ℂ ↦ 1-z)
          (by fun_prop)).continuous)
        hN' hn' (x := 1/2) le_rfl (by norm_num)
  have his : Integrable (fun t : ℝ ↦ F t * G (-t)) := by
    simpa using hi'.comp_mul_left' (show (-1:ℝ) ≠ 0 by norm_num)
  have he : (∫ t : ℝ, F (-t) * G t) = ∫ t : ℝ, F t * G (-t) := by
    simpa using (integral_neg_eq_self (fun t : ℝ ↦ F t * G (-t)) volume)
  simp_rw [pairedWeight, hr, weight_critical, add_mul]
  rw [integral_add hi hi', he, ← integral_add hi his]
  apply integral_congr_ae
  filter_upwards with t
  dsimp [F,G]
  rw [← mul_add, ← WeilExplicit.gamma_pair t]
  rw [ofReal_neg, neg_mul, ← sub_eq_add_neg]

end WeilExplicit
