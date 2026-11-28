import Masullo.QRH.MeanSquare.CosetPoisson
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Distribution.TemperateGrowth

/-! # A band-limited majorant for the first Poisson step

`exists_transferMajorant` gives a real Schwartz function `P` with `P ≥ 0` on `[0, ∞)`,
`P ≥ 1` on `[0, 1]`, and `gaoZhaoTransform P t = 0` for `|t| ≥ 1`.

Construction. `bump` is a smooth radial bump on `ℂ` supported in the disc of radius `1/8`, and
`profile = 𝓕 bump` is real and radial. On the disc of radius `1` it is at least half the mass of
`bump`. The square `profile²` is the Fourier transform of `bump ⋆ bump`, so its Fourier
transform is supported in the disc of radius `1/4`. Its radial profile `r ↦ profile(√r)²` is
made a Schwartz function on `ℝ` in two pieces:

* near `[0, 2]`, `profile(√r) = series r`, an entire power series in `r` built from the even
  moments of `bump`;
* on `[2, ∞)`, `profile(√r) = profile(root r)` with `root` a temperate function equal to `√` there,
  so composition with `root` preserves the Schwartz class.

`fourier_radialSchwartz` converts the Fourier transform on `ℂ` to `gaoZhaoTransform`.
-/

noncomputable section

open MeasureTheory Set Function Filter
open scoped ContDiff Real FourierTransform SchwartzMap Topology

namespace Masullo.QRH.MeanSquare.Majorant

/-! ### A temperate square root -/

/-- A smooth step from `0` on `(-∞, 1]` to `1` on `[2, ∞)`. -/
def step (r : ℝ) : ℝ := Real.smoothTransition (r - 1)

lemma contDiff_step : ContDiff ℝ ∞ step :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

lemma fderiv_step_eq_zero {x : ℝ} (hx : x ∉ Icc 1 2) : fderiv ℝ step x = 0 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · have : step =ᶠ[𝓝 x] fun _ ↦ 0 := eventually_of_mem (Iio_mem_nhds h) fun y hy ↦
      Real.smoothTransition.zero_of_nonpos (by simp only [mem_Iio] at hy; linarith)
    rw [this.fderiv_eq, fderiv_const_apply]
  · have : step =ᶠ[𝓝 x] fun _ ↦ 1 := eventually_of_mem (Ioi_mem_nhds h) fun y hy ↦
      Real.smoothTransition.one_of_one_le (by simp only [mem_Ioi] at hy; linarith)
    rw [this.fderiv_eq, fderiv_const_apply]

lemma hasTemperateGrowth_step : step.HasTemperateGrowth := by
  refine .of_fderiv (k := 0) (C := 1) ?_ (contDiff_step.differentiable (by simp)) fun x ↦ ?_
  · refine HasCompactSupport.hasTemperateGrowth ?_ (contDiff_step.fderiv_right (m := ∞) ?_)
    · exact HasCompactSupport.intro isCompact_Icc fun x hx ↦ fderiv_step_eq_zero hx
    · exact le_of_eq rfl
  · simp [step, abs_of_nonneg (Real.smoothTransition.nonneg _), Real.smoothTransition.le_one]

/-- `r` for `r ≥ 2`, `1 + r²` for `r ≤ 1`, and at least `max 1 |r|` everywhere. -/
def stretch (r : ℝ) : ℝ := step r * r + (1 - step r) * (1 + r ^ 2)

lemma stretch_of_two_le {r : ℝ} (hr : 2 ≤ r) : stretch r = r := by
  simp [stretch, step, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ r - 1)]

lemma one_le_stretch (r : ℝ) : 1 ≤ stretch r ∧ |r| ≤ stretch r := by
  have h0 := Real.smoothTransition.nonneg (r - 1)
  have h1 := Real.smoothTransition.le_one (r - 1)
  rcases le_or_gt r 1 with hr | hr
  · have : step r = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    simp only [stretch, this, zero_mul, sub_zero, one_mul, zero_add]
    exact ⟨by nlinarith, by cases abs_cases r <;> nlinarith⟩
  · simp only [stretch, step, abs_of_pos (by linarith : 0 < r)]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hr.le h0,
      mul_le_mul_of_nonneg_left (by nlinarith : r ≤ 1 + r ^ 2) (by linarith : 0 ≤ 1 -
        Real.smoothTransition (r - 1))]

lemma hasTemperateGrowth_stretch : stretch.HasTemperateGrowth :=
  (hasTemperateGrowth_step.mul .id').add
    (((HasTemperateGrowth.const 1).sub hasTemperateGrowth_step).mul
      ((HasTemperateGrowth.const 1).add (HasTemperateGrowth.id'.pow 2)))

/-- `√r` for `r ≥ 2`, smooth and of temperate growth on `ℝ`. -/
def root (r : ℝ) : ℝ := √(stretch r)

lemma root_of_two_le {r : ℝ} (hr : 2 ≤ r) : root r = √r := by rw [root, stretch_of_two_le hr]

lemma abs_le_root (r : ℝ) : ‖r‖ ≤ 1 * (1 + ‖root r‖) ^ 2 := by
  have h := (one_le_stretch r).2
  have hs := Real.sq_sqrt (zero_le_one.trans (one_le_stretch r).1)
  rw [root, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), one_mul]
  nlinarith [Real.sqrt_nonneg (stretch r)]

/-- The derivatives of `y ↦ y ^ (1/2)` on `(1/2, ∞)` grow at most linearly. -/
lemma rpow_half_bound (N : ℕ) : ∃ (k : ℕ) (C : ℝ), ∃ (_ : 0 ≤ C), ∀ n ≤ N, ∀ x ∈ Ioi (1 / 2 : ℝ),
    ‖iteratedFDerivWithin ℝ n (fun y : ℝ ↦ y ^ (1 / 2 : ℝ)) (Ioi (1 / 2)) x‖ ≤
      C * (1 + ‖x‖) ^ k := by
  have hunique : UniqueDiffOn ℝ (Ioi (1 / 2 : ℝ)) := isOpen_Ioi.uniqueDiffOn
  refine ⟨1, (∑ k ∈ Finset.range (N + 1), ‖Polynomial.eval (1 / 2 : ℝ) (descPochhammer ℝ k)‖) *
    2 ^ N, by positivity, fun n hn x hx ↦ ?_⟩
  have hx' : (1 / 2 : ℝ) < x := hx
  have hx0 : 0 < x := lt_trans (by norm_num) hx'
  have : ContDiffAt ℝ n (fun y : ℝ ↦ y ^ (1 / 2 : ℝ)) x :=
    Real.contDiffAt_rpow_const <| Or.inl hx0.ne'
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_eq_iteratedDeriv hunique this hx, iteratedDeriv_eq_iterate,
    Real.iter_deriv_rpow_const, norm_mul, mul_assoc]
  gcongr 1
  · exact Finset.single_le_sum (f := fun k ↦ ‖Polynomial.eval (1 / 2 : ℝ) (descPochhammer ℝ k)‖)
      (fun _ _ ↦ by positivity) (Finset.mem_range.mpr (by omega))
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _), Real.norm_eq_abs,
    abs_of_pos hx0, pow_one]
  rcases le_or_gt 1 x with h1 | h1
  · calc x ^ (1 / 2 - n : ℝ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by
          have : (0 : ℝ) ≤ n := n.cast_nonneg
          linarith)
      _ ≤ 2 ^ N * (1 + x) := by
          rw [Real.rpow_one]
          nlinarith [one_le_pow₀ (n := N) (by norm_num : (1 : ℝ) ≤ 2)]
  · calc x ^ (1 / 2 - n : ℝ) ≤ x ^ (-(N : ℝ)) := Real.rpow_le_rpow_of_exponent_ge hx0 h1.le (by
          have : (n : ℝ) ≤ N := by exact_mod_cast hn
          linarith)
      _ = (x⁻¹) ^ N := by rw [Real.rpow_neg hx0.le, Real.rpow_natCast, inv_pow]
      _ ≤ 2 ^ N := by
          gcongr
          rw [inv_le_comm₀ hx0 (by norm_num)]
          linarith
      _ ≤ 2 ^ N * (1 + x) := le_mul_of_one_le_right (by positivity) (by linarith)

lemma hasTemperateGrowth_root : root.HasTemperateGrowth := by
  have ht : range stretch ⊆ Ioi (1 / 2 : ℝ) := by
    rintro - ⟨r, rfl⟩
    exact lt_of_lt_of_le (by norm_num : (1 / 2 : ℝ) < 1) (one_le_stretch r).1
  have hdiff : ContDiffOn ℝ ∞ (fun y : ℝ ↦ y ^ (1 / 2 : ℝ)) (Ioi (1 / 2)) :=
    contDiffOn_fun_id.rpow_const_of_ne fun x hx ↦
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hx).ne'
  have := HasTemperateGrowth.comp' ht isOpen_Ioi.uniqueDiffOn hdiff rpow_half_bound
    hasTemperateGrowth_stretch
  convert this using 1
  ext r
  simp [root, Real.sqrt_eq_rpow]

/-! ### A radial bump on `ℂ` and its Fourier transform -/

/-- A smooth radial bump, positive exactly on the open disc of radius `1/8`. -/
def bump (ξ : ℂ) : ℝ := Real.smoothTransition (1 / 64 - ‖ξ‖ ^ 2)

lemma contDiff_bump : ContDiff ℝ ∞ bump :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ))

lemma continuous_bump : Continuous bump := contDiff_bump.continuous

lemma bump_nonneg (ξ : ℂ) : 0 ≤ bump ξ := Real.smoothTransition.nonneg _

lemma norm_lt_of_bump_ne_zero {ξ : ℂ} (h : bump ξ ≠ 0) : ‖ξ‖ < 1 / 8 := by
  by_contra! h'
  exact h (Real.smoothTransition.zero_of_nonpos (by nlinarith))

lemma hasCompactSupport_bump : HasCompactSupport bump :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (1 / 8)) fun ξ hξ ↦ by
    by_contra h
    exact hξ (mem_closedBall_zero_iff.mpr (norm_lt_of_bump_ne_zero h).le)

lemma bump_mul_circle (a : Circle) (ξ : ℂ) : bump (a * ξ) = bump ξ := by
  simp [bump]

lemma bump_neg (ξ : ℂ) : bump (-ξ) = bump ξ := by simp [bump]

/-- The total mass of `bump`. -/
def mass : ℝ := ∫ ξ, bump ξ

lemma mass_pos : 0 < mass :=
  continuous_bump.integral_pos_of_hasCompactSupport_nonneg_ne_zero hasCompactSupport_bump
    bump_nonneg (x := 0) (Real.smoothTransition.pos_of_pos (by norm_num)).ne'

lemma integrable_bump_mul {f : ℂ → ℝ} (hf : Continuous f) : Integrable fun ξ ↦ bump ξ * f ξ :=
  (continuous_bump.mul hf).integrable_of_hasCompactSupport hasCompactSupport_bump.mul_right

/-- `bump` as a Schwartz function. -/
def bumpS : 𝓢(ℂ, ℂ) :=
  (hasCompactSupport_bump.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp contDiff_bump)

lemma bumpS_apply (ξ : ℂ) : bumpS ξ = bump ξ := rfl

/-- The real Fourier transform of `bump`. -/
def profile (z : ℂ) : ℝ := ∫ ξ, bump ξ * Real.cos (2 * π * inner ℝ ξ z)

lemma integral_bump_mul_sin (z : ℂ) : ∫ ξ, bump ξ * Real.sin (2 * π * inner ℝ ξ z) = 0 := by
  have h := integral_neg_eq_self (fun ξ ↦ bump ξ * Real.sin (2 * π * inner ℝ ξ z)) volume
  simp only [bump_neg, inner_neg_left, mul_neg, Real.sin_neg, integral_neg] at h
  linarith

lemma fourier_bumpS (z : ℂ) : 𝓕 bumpS z = profile z := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  set c : ℂ → ℝ := fun ξ ↦ bump ξ * Real.cos (2 * π * inner ℝ ξ z)
  set s : ℂ → ℝ := fun ξ ↦ bump ξ * Real.sin (2 * π * inner ℝ ξ z) with hsdef
  have hc : Integrable (fun ξ ↦ (c ξ : ℂ)) :=
    (integrable_bump_mul (f := fun ξ ↦ Real.cos (2 * π * inner ℝ ξ z)) (by fun_prop)).ofReal
  have hs : Integrable (fun ξ ↦ Complex.I * (s ξ : ℂ)) :=
    (integrable_bump_mul (f := fun ξ ↦ Real.sin (2 * π * inner ℝ ξ z))
      (by fun_prop)).ofReal.const_mul _
  have : ∀ ξ : ℂ, 𝐞 (-inner ℝ ξ z) • bumpS ξ = (c ξ : ℂ) - Complex.I * (s ξ : ℂ) := by
    intro ξ
    rw [bumpS_apply, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul,
      show ((2 * π * -inner ℝ ξ z : ℝ) : ℂ) = ((-(2 * π * inner ℝ ξ z) : ℝ) : ℂ) by ring_nf,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    simp only [c, s]
    push_cast
    ring
  rw [integral_congr_ae (Eventually.of_forall this), integral_sub hc hs, integral_const_mul,
    integral_complex_ofReal, integral_complex_ofReal, hsdef, integral_bump_mul_sin]
  simp only [Complex.ofReal_zero, mul_zero, sub_zero]
  rfl

lemma inner_mul_circle (a : Circle) (ξ z : ℂ) :
    inner ℝ ξ (a * z) = inner ℝ ((starRingEnd ℂ) (a : ℂ) * ξ) z := by
  simp [Complex.inner]
  ring

lemma profile_mul_circle (a : Circle) (z : ℂ) : profile (a * z) = profile z := by
  have h := (rotation a).measurePreserving.integral_comp
    (rotation a).toHomeomorph.measurableEmbedding
    (fun ξ ↦ bump ξ * Real.cos (2 * π * inner ℝ ((starRingEnd ℂ) (a : ℂ) * ξ) z))
  simp only [rotation_apply] at h
  simp only [profile, inner_mul_circle]
  refine Eq.trans h.symm (integral_congr_ae (Eventually.of_forall fun ξ ↦ ?_))
  simp only
  rw [bump_mul_circle, ← mul_assoc, Complex.conj_mul', Circle.norm_coe, Complex.ofReal_one,
    one_pow, one_mul]

lemma profile_norm (z : ℂ) : profile z = profile (‖z‖ : ℂ) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
  rw [mul_comm, ← Circle.coe_exp, profile_mul_circle]

lemma half_mass_le_profile {z : ℂ} (hz : ‖z‖ ≤ 1) : mass / 2 ≤ profile z := by
  rw [mass, ← integral_div]
  refine integral_mono ((integrable_bump_mul (f := fun _ ↦ 1) continuous_const).div_const 2
    |>.congr (by simp)) (integrable_bump_mul (by fun_prop)) fun ξ ↦ ?_
  dsimp only
  rcases eq_or_ne (bump ξ) 0 with h | h
  · simp [h]
  have hξ := norm_lt_of_bump_ne_zero h
  have hθ : |2 * π * inner ℝ ξ z| ≤ 1 := by
    rw [abs_mul, abs_of_pos (by positivity)]
    have := abs_real_inner_le_norm ξ z
    have := Real.pi_lt_four
    have : ‖ξ‖ * ‖z‖ ≤ 1 / 8 := by nlinarith [norm_nonneg ξ, norm_nonneg z]
    nlinarith [abs_nonneg (inner ℝ ξ z)]
  have hc : 1 / 2 ≤ Real.cos (2 * π * inner ℝ ξ z) := by
    have := Real.one_sub_sq_div_two_le_cos (x := 2 * π * inner ℝ ξ z)
    have : (2 * π * inner ℝ ξ z) ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (2 * π * inner ℝ ξ z)]
    linarith
  nlinarith [bump_nonneg ξ]

/-! ### The profile as an entire power series in `|z|²` -/

/-- The even moments of `bump` in the first coordinate. -/
def moment (k : ℕ) : ℝ := ∫ ξ, bump ξ * ξ.re ^ (2 * k)

lemma moment_nonneg (k : ℕ) : 0 ≤ moment k :=
  integral_nonneg fun ξ ↦ mul_nonneg (bump_nonneg ξ) (by rw [pow_mul]; positivity)

lemma moment_le (k : ℕ) : moment k ≤ mass / 64 ^ k := by
  rw [mass, ← integral_div]
  refine integral_mono (integrable_bump_mul (by fun_prop))
    ((continuous_bump.integrable_of_hasCompactSupport hasCompactSupport_bump).div_const _)
    fun ξ ↦ ?_
  dsimp only
  rcases eq_or_ne (bump ξ) 0 with h | h
  · simp [h]
  have hξ := norm_lt_of_bump_ne_zero h
  have : ξ.re ^ (2 * k) ≤ (1 / 64) ^ k := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (sq_nonneg _)
    have := Complex.abs_re_le_norm ξ
    nlinarith [abs_nonneg ξ.re, sq_abs ξ.re]
  rw [div_eq_mul_inv, ← inv_pow, ← one_div]
  exact mul_le_mul_of_nonneg_left this (bump_nonneg ξ)

/-- The Taylor coefficients of `r ↦ profile (√r)`. -/
def coeff (k : ℕ) : ℝ := (-1) ^ k * (2 * π) ^ (2 * k) / (2 * k).factorial * moment k

lemma abs_coeff (k : ℕ) : |coeff k| = (2 * π) ^ (2 * k) / (2 * k).factorial * moment k := by
  rw [coeff, abs_mul, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (2 * π) ^ (2 * k)), Nat.abs_cast,
    abs_of_nonneg (moment_nonneg k)]

lemma abs_coeff_mul_le (k : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    |coeff k| * s ^ k ≤ mass * ((π ^ 2 * s / 16) ^ k / k.factorial) := by
  have hf : (k.factorial : ℝ) ≤ (2 * k).factorial := by exact_mod_cast Nat.factorial_le (by omega)
  have hk : (0 : ℝ) < k.factorial := by positivity
  rw [abs_coeff]
  calc (2 * π) ^ (2 * k) / (2 * k).factorial * moment k * s ^ k
      ≤ (2 * π) ^ (2 * k) / k.factorial * (mass / 64 ^ k) * s ^ k := by
        gcongr <;> first | exact moment_le k | exact moment_nonneg k
    _ = mass * ((π ^ 2 * s / 16) ^ k / k.factorial) := by
        rw [pow_mul, div_pow, mul_pow, mul_pow,
          show (64 : ℝ) ^ k = 4 ^ k * 16 ^ k by rw [← mul_pow]; norm_num]
        field_simp
        ring

/-- The profile in the variable `r = |z|²`, an entire power series. -/
def series : ℝ → ℝ := FormalMultilinearSeries.ofScalarsSum coeff

lemma radius_ofScalars_coeff : (FormalMultilinearSeries.ofScalars ℝ coeff).radius = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  refine FormalMultilinearSeries.le_radius_of_bound _ (mass * Real.exp (π ^ 2 * r / 16))
    fun n ↦ ?_
  rw [FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs]
  refine (abs_coeff_mul_le n r.2).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.pow_div_factorial_le_exp (π ^ 2 * (r : ℝ) / 16) (by positivity) n) mass_pos.le

lemma contDiff_series : ContDiff ℝ ∞ series := by
  have h := (FormalMultilinearSeries.ofScalars ℝ coeff).hasFPowerSeriesOnBall
    (by simp [radius_ofScalars_coeff])
  rw [radius_ofScalars_coeff] at h
  exact AnalyticOnNhd.contDiff fun x _ ↦ h.analyticAt_of_mem (by simp)

lemma series_apply (r : ℝ) : series r = ∑' k, coeff k * r ^ k := by
  simp [series, FormalMultilinearSeries.ofScalarsSum_eq_tsum, mul_comm]

lemma profile_ofReal (x : ℝ) : profile x = series (x ^ 2) := by
  have hin : ∀ ξ : ℂ, inner ℝ ξ (x : ℂ) = x * ξ.re := fun ξ ↦ by
    simp [Complex.inner, mul_comm]
  set F : ℕ → ℂ → ℝ := fun k ξ ↦
    bump ξ * ((-1) ^ k * (2 * π * inner ℝ ξ (x : ℂ)) ^ (2 * k) / (2 * k).factorial)
  have hF : ∀ k ξ, F k ξ = ((-1) ^ k * (2 * π) ^ (2 * k) / (2 * k).factorial * (x ^ 2) ^ k) *
      (bump ξ * ξ.re ^ (2 * k)) := fun k ξ ↦ by
    simp only [F, hin]
    rw [← pow_mul]
    ring
  have hF' : ∀ k ξ, ‖F k ξ‖ = ((2 * π) ^ (2 * k) / (2 * k).factorial * (x ^ 2) ^ k) *
      (bump ξ * ξ.re ^ (2 * k)) := fun k ξ ↦ by
    rw [hF, norm_mul, Real.norm_of_nonneg (mul_nonneg (bump_nonneg ξ)
      (by rw [pow_mul]; positivity))]
    congr 1
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (by positivity : (0 : ℝ) < (2 * π) ^ (2 * k)), Nat.abs_cast,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (x ^ 2) ^ k)]
  have hint : ∀ k, Integrable (F k) := fun k ↦ by
    rw [funext (hF k)]; exact (integrable_bump_mul (by fun_prop)).const_mul _
  have hsum : Summable fun k ↦ ∫ ξ, ‖F k ξ‖ := by
    refine Summable.of_nonneg_of_le (fun k ↦ integral_nonneg fun ξ ↦ norm_nonneg _)
      (fun k ↦ ?_) ((Real.summable_pow_div_factorial (π ^ 2 * x ^ 2 / 16)).mul_left mass)
    simp_rw [hF']
    rw [integral_const_mul]
    have := abs_coeff_mul_le k (sq_nonneg x)
    rw [abs_coeff, moment] at this
    linarith
  have hcos : ∀ ξ, ∑' k, F k ξ = bump ξ * Real.cos (2 * π * inner ℝ ξ (x : ℂ)) := fun ξ ↦ by
    simp only [F]
    rw [tsum_mul_left, (Real.hasSum_cos _).tsum_eq]
  have hint' : ∀ k, ∫ ξ, F k ξ = coeff k * (x ^ 2) ^ k := fun k ↦ by
    rw [funext (hF k), integral_const_mul, coeff, moment]
    ring
  calc profile x = ∫ ξ, ∑' k, F k ξ := by
        rw [profile]; congr 1 with ξ; exact (hcos ξ).symm
    _ = ∑' k, ∫ ξ, F k ξ := (integral_tsum_of_summable_integral_norm hint hsum).symm
    _ = series (x ^ 2) := by rw [series_apply]; congr 1 with k; exact hint' k

/-! ### The majorant -/

/-- A cutoff equal to `1` on `[-2, 2]` and supported in `(-3, 3)`. -/
def cut : ContDiffBump (0 : ℝ) := ⟨2, 3, by norm_num, by norm_num⟩

lemma cut_eq_one {r : ℝ} (h : |r| ≤ 2) : cut r = 1 :=
  cut.one_of_mem_closedBall (by rw [mem_closedBall_zero_iff, Real.norm_eq_abs]; exact h)

lemma hasTemperateGrowth_one_sub_cut : (fun r : ℝ ↦ 1 - cut r).HasTemperateGrowth :=
  (HasTemperateGrowth.const 1).sub (cut.hasCompactSupport.hasTemperateGrowth cut.contDiff)

/-- A smooth function on `ℝ` equal to `r ↦ profile √r` on `[0, ∞)`. -/
def radialProfile (r : ℝ) : ℝ := cut r * series r + (1 - cut r) * profile (root r)

lemma radialProfile_of_nonneg {r : ℝ} (hr : 0 ≤ r) : radialProfile r = profile (√r) := by
  have hs : series r = profile (√r) := by rw [profile_ofReal, Real.sq_sqrt hr]
  rcases le_or_gt r 2 with h | h
  · simp [radialProfile, cut_eq_one (by rw [abs_of_nonneg hr]; exact h), hs]
  · rw [radialProfile, root_of_two_le h.le, hs]
    ring

/-- The compactly supported part of `radialProfile`. -/
def nearS : 𝓢(ℝ, ℂ) :=
  ((cut.hasCompactSupport.mul_right (f' := series)).comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (cut.contDiff.mul contDiff_series))

/-- `profile` on the real line, as a Schwartz function. -/
def lineS : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℂ Complex.hasTemperateGrowth_ofReal ⟨1, 1, fun x ↦ by simp⟩ (𝓕 bumpS)

/-- The part of `radialProfile` away from the origin. -/
def farS : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun r : ℝ ↦ 1 - cut r)
    (SchwartzMap.compCLM ℂ hasTemperateGrowth_root ⟨2, 1, abs_le_root⟩ lineS)

/-- `radialProfile` as a Schwartz function. -/
def radialS : 𝓢(ℝ, ℂ) := nearS + farS

lemma radialS_apply (r : ℝ) : radialS r = radialProfile r := by
  simp [radialS, nearS, farS, lineS, radialProfile, SchwartzMap.smulLeftCLM_apply_apply
    hasTemperateGrowth_one_sub_cut, SchwartzMap.compCLM_apply, fourier_bumpS]

/-- The majorant: `r ↦ (4 / mass²) profile(√r)²` on `[0, ∞)`. -/
def majorant : 𝓢(ℝ, ℂ) :=
  ((4 / mass ^ 2 : ℝ) : ℂ) • SchwartzMap.smulLeftCLM ℂ (⇑radialS) radialS

lemma majorant_apply (r : ℝ) : majorant r = ((4 / mass ^ 2 * radialProfile r ^ 2 : ℝ) : ℂ) := by
  rw [majorant, smul_apply, SchwartzMap.smulLeftCLM_apply_apply
    radialS.hasTemperateGrowth, radialS_apply, smul_eq_mul, smul_eq_mul]
  push_cast
  ring

/-- The convolution square of `bump`, supported in the disc of radius `1/4`. -/
def bumpConv : 𝓢(ℂ, ℂ) := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) bumpS bumpS

lemma bumpConv_eq_zero {ξ : ℂ} (hξ : 1 / 4 ≤ ‖ξ‖) : bumpConv ξ = 0 := by
  rw [bumpConv, SchwartzMap.convolution_apply]
  by_contra h
  obtain ⟨a, ha, b, hb, hab⟩ := support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ) h
  have ha' := norm_lt_of_bump_ne_zero (ξ := a) fun h0 ↦
    ha (by rw [bumpS_apply, h0, Complex.ofReal_zero])
  have hb' := norm_lt_of_bump_ne_zero (ξ := b) fun h0 ↦
    hb (by rw [bumpS_apply, h0, Complex.ofReal_zero])
  have := norm_add_le a b
  simp only at hab
  rw [hab] at this
  linarith

lemma fourier_fourier (f : 𝓢(ℂ, ℂ)) (ξ : ℂ) : 𝓕 (𝓕 f) ξ = f (-ξ) := by
  have h := congrArg (fun g : 𝓢(ℂ, ℂ) ↦ g (-ξ))
    (FourierTransform.fourierInv_fourier_eq (F := 𝓢(ℂ, ℂ)) f)
  simp only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg] at h
  rw [← h, SchwartzMap.fourier_coe]

lemma radialSchwartz_majorant :
    radialSchwartz majorant one_pos = ((4 / mass ^ 2 : ℝ) : ℂ) • 𝓕 bumpConv := by
  ext z
  rw [radialSchwartz_apply, majorant_apply, div_one, radialProfile_of_nonneg
    (Complex.normSq_nonneg z), ← Complex.norm_def, ← profile_norm, smul_apply,
    bumpConv, SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply, fourier_bumpS,
    smul_eq_mul, ContinuousLinearMap.mul_apply']
  push_cast
  ring

lemma gaoZhaoTransform_majorant {t : ℝ} (ht : 1 ≤ t) : gaoZhaoTransform majorant t = 0 := by
  have h3 : (0 : ℝ) < √3 := by positivity
  set ξ : ℂ := ((2 * t / √3 : ℝ) : ℂ)
  have hξ : ‖ξ‖ = 2 * t / √3 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h := fourier_radialSchwartz majorant one_pos ξ
  rw [radialSchwartz_majorant, FourierTransform.fourier_smul, smul_apply,
    fourier_fourier,
    bumpConv_eq_zero (by
      rw [norm_neg, hξ, le_div_iff₀ h3]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]), hξ, Real.sqrt_one, one_mul,
    show 2 * t / √3 * (√3 / 2) = t by field_simp] at h
  rw [smul_zero, Complex.ofReal_one, one_mul, eq_comm, mul_eq_zero] at h
  exact h.resolve_left (div_ne_zero (Complex.ofReal_ne_zero.mpr h3.ne') two_ne_zero)

lemma gaoZhaoTransform_neg (W : 𝓢(ℝ, ℂ)) (t : ℝ) :
    gaoZhaoTransform W (-t) = gaoZhaoTransform W t := by
  rw [gaoZhaoTransform, gaoZhaoTransform]
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun xy ↦ ?_)
  dsimp only
  have e : (((-xy).1 : ℝ) : ℂ) + (((-xy).2 : ℝ) : ℂ) * (1 + eisEmbedding eisOmega) =
      -((xy.1 : ℂ) + xy.2 * (1 + eisEmbedding eisOmega)) := by
    simp only [Prod.fst_neg, Prod.snd_neg, Complex.ofReal_neg]
    ring
  rw [e, Complex.normSq_neg]
  congr 2
  push_cast
  ring

end Masullo.QRH.MeanSquare.Majorant

namespace Masullo.QRH.MeanSquare

open Majorant

/-- A band-limited Schwartz majorant of the indicator of `[0, 1]`: `P` is real, nonnegative on
`[0, ∞)`, at least `1` on `[0, 1]`, and its radial transform in Gao–Zhao's coordinates vanishes
for `|t| ≥ 1`. -/
theorem exists_transferMajorant : ∃ P : SchwartzMap ℝ ℂ,
    (∀ x, (P x).im = 0) ∧ (∀ x, 0 ≤ x → 0 ≤ (P x).re) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, 1 ≤ (P x).re) ∧ ∀ t, 1 ≤ |t| → gaoZhaoTransform P t = 0 := by
  refine ⟨majorant, fun x ↦ by rw [majorant_apply, Complex.ofReal_im],
    fun x _ ↦ by rw [majorant_apply, Complex.ofReal_re]; positivity, fun x hx ↦ ?_,
    fun t ht ↦ ?_⟩
  · rw [majorant_apply, Complex.ofReal_re, radialProfile_of_nonneg hx.1]
    have h1 : ‖((√x : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg x)]
      exact Real.sqrt_le_one.mpr hx.2
    have h := half_mass_le_profile h1
    have hm := mass_pos
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  · rcases le_total 0 t with h0 | h0
    · exact gaoZhaoTransform_majorant (by rwa [abs_of_nonneg h0] at ht)
    · rw [← neg_neg t, gaoZhaoTransform_neg]
      exact gaoZhaoTransform_majorant (by rwa [abs_of_nonpos h0] at ht)

end Masullo.QRH.MeanSquare
