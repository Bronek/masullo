import WeilExplicit.GammaFactor
import WeilExplicit.PrimeIntegral

/-! # Bounds for the vertical contour integrands -/

namespace WeilExplicit

open WeilExplicit (weight)

open Complex MeasureTheory Set Real

/-- The test weight decays quadratically with height, uniformly across the rectangle. -/
theorem weight_strip_decay {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hs : HasCompactSupport k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖weight k z‖ ≤ M / (1+z.im^2) := by
  obtain ⟨M,hM,h⟩ := transform_decay hk hs 2
  refine ⟨M,hM,fun z ha hb ↦ (h ((z-1/2)/I) ?_).trans ?_⟩
  · simp [div_I]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · gcongr
    simp [normSq_apply, div_I]
    nlinarith [sq_nonneg (z.re-1/2)]

/-- The reflected test weight has the same quadratic decay on the symmetric strip. -/
theorem reflected_weight_strip_decay {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hs : HasCompactSupport k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖weight k (1-z)‖ ≤ M/(1+z.im^2) := by
  obtain ⟨M,hM,h⟩ := weight_strip_decay hk hs
  exact ⟨M,hM,fun z ha hb ↦ by simpa using h (1-z) (by simp; linarith) (by simp; linarith)⟩

/-- The numerator appearing after reflection of the left vertical line. -/
noncomputable def pairedWeight (k : ℝ → ℂ) (s : ℂ) := weight k s + weight k (1-s)

/-- The sum of the original and reflected weights is entire. -/
theorem differentiable_pairedWeight {k : ℝ → ℂ} (hk : Continuous k) (hs : HasCompactSupport k) :
    Differentiable ℂ (pairedWeight k) :=
  (differentiable_weight hk hs).add ((differentiable_weight hk hs).comp (by fun_prop))

/-- The sum of the two weights decays quadratically on the whole contour strip. -/
theorem pairedWeight_strip_decay {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hs : HasCompactSupport k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖pairedWeight k z‖ ≤ M / (1+z.im^2) := by
  obtain ⟨M,hM,h⟩ := weight_strip_decay hk hs
  refine ⟨M+M,by positivity,fun z ha hb ↦ ?_⟩
  have h' := h (1-z) (by simp; linarith) (by simp; linarith)
  simpa [pairedWeight, add_div] using (norm_add_le (weight k z) (weight k (1-z))).trans
    (add_le_add (h z ha hb) h')

/-- The square-root majorant on a vertical line is at least one at every height. -/
protected theorem sqrt_one_add_abs_ge_one (t : ℝ) : 1 ≤ √(1+|t|) :=
  Real.one_le_sqrt.mpr (by linarith [abs_nonneg t])

/-- Above height one the square-root majorant is bounded by twice the height. -/
protected theorem sqrt_one_add_le_two_mul {T : ℝ} (hT : 1 ≤ T) : √(1+T) ≤ 2*T := by
  apply (Real.sqrt_le_iff).2
  exact ⟨by linarith, by nlinarith [sq_nonneg (T-1)]⟩

/-- The Gamma logarithmic derivative grows at most as √(1+|Im s|) for 1/2 ≤ Re s ≤ 2. -/
theorem gamma_strip_bound : ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 1/2 ≤ s.re → s.re ≤ 2 →
    ‖logDeriv Gammaℝ s‖ ≤ A*√(1+|s.im|) := by
  refine ⟨30+|Real.log π|,by positivity,fun s ha hb ↦ ?_⟩
  rw [logDeriv_gamma_factor (by linarith), norm_div]
  have h := (norm_sub_le (digamma (s/2)) (Real.log π : ℂ)).trans
    (add_le_add (norm_digamma_half_le ha hb) (le_refl _))
  simp only [Complex.norm_real, Real.norm_eq_abs] at h
  have h' := le_mul_of_one_le_right (abs_nonneg (Real.log π))
    (WeilExplicit.sqrt_one_add_abs_ge_one s.im)
  rw [Complex.norm_ofNat, div_le_iff₀ (by norm_num)]
  nlinarith [sqrt_nonneg (1+|s.im|), mul_nonneg (abs_nonneg (Real.log π)) (sqrt_nonneg (1+|s.im|))]

/-- The Gamma logarithmic derivative is holomorphic on Re s > 0. -/
theorem analyticAt_logDeriv_gamma {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ (logDeriv Gammaℝ) z :=
  (analyticAt_Gammaℝ hz).deriv.div (analyticAt_Gammaℝ hz) (Gammaℝ_ne_zero_of_re_pos hz)

/-- The zeta logarithmic derivative is holomorphic on Re s > 1. -/
theorem analyticAt_logDeriv_zeta {z : ℂ} (hz : 1 < z.re) :
    AnalyticAt ℂ (logDeriv riemannZeta) z := by
  have ha := analyticOn_riemannZeta z (show z ≠ 1 from fun h ↦ by simp [h] at hz)
  exact ha.deriv.div ha (riemannZeta_ne_zero_of_one_le_re hz.le)

/-- A quadratic-decay weight times a square-root growth factor is integrable on a vertical line. -/
theorem integrable_line_mul {W D : ℂ → ℂ} {c M A : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hW : Continuous W) (hD : ∀ t : ℝ, ContinuousAt D (c+t*I))
    (hw : ∀ t : ℝ, ‖W (c+t*I)‖ ≤ M/(1+t^2)) (hd : ∀ t : ℝ, ‖D (c+t*I)‖ ≤ A*√(1+|t|)) :
    Integrable (fun t : ℝ ↦ W (c+t*I)*D (c+t*I)) := by
  apply integrable_of_quadratic_decay (M := M*A) (mul_nonneg hM hA)
  · exact (hW.comp (by fun_prop)).mul
      (continuous_iff_continuousAt.mpr fun t ↦ (hD t).comp (f := fun t : ℝ ↦ c+t*I) (by fun_prop))
  · intro t
    rw [norm_mul]
    exact (mul_le_mul (hw t) (hd t) (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- At height T > 0, the product of the weight and derivative is bounded in norm by MA/T. -/
protected theorem horizontal_product_bound {W D : ℂ} {M A T : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (hw : ‖W‖ ≤ M/(1+T^2)) (hd : ‖D‖ ≤ A*T) : ‖W*D‖ ≤ M*A/T := by
  rw [norm_mul]
  calc
    _ ≤ (M/T^2) * (A*T) :=
      mul_le_mul (hw.trans (by gcongr; linarith)) hd (norm_nonneg _) (by positivity)
    _ = _ := by field_simp

end WeilExplicit
