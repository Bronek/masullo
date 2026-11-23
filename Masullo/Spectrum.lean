import Masullo.Strength

/-!
# Spectrum of the theta quotient

`W a` is the `L²` space of the measure `2 cosh (2 a x) dx` and `V a` is the closed span of the theta
functions in it. For `|Re z| < a` the moments `u ↦ ∫ u(x) x^m e^{zx} dx` are continuous on `W a`.
They annihilate `V a` exactly when `ζ` has a zero of order greater than `m` at `1/2 + z` in the
critical strip. No position of any zero is assumed or concluded.

Poisson summation gives rapid decay of theta functions at both ends, so their moments are entire
in `z`. The identity with `ζ` times a Mellin transform is the Dirichlet series for `Re z > 1/2` and
extends to `Re z > -1/2` by the identity theorem. Poisson summation also reflects `z` to `-z`, which
covers the rest of the strip `|Re z| < a` when `a > 1/2`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped InnerProductSpace SchwartzMap FourierTransform ComplexConjugate

namespace Masullo.Spectrum

/-! ### Theta functions -/

/-- `x ↦ e^(x/2) ∑_{n ≥ 1} f(n e^x)`. -/
noncomputable def theta (f : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  Real.exp (x / 2) * ∑' n : ℕ, f ((n + 1) * Real.exp x)

/-- Even Schwartz functions with `f 0 = ∫ f = 0`. -/
structure ThetaClass (f : 𝓢(ℝ, ℂ)) : Prop where
  even : ∀ x, f (-x) = f x
  zero : f 0 = 0
  integral : ∫ x, f x = 0

lemma integrable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable fun x : ℝ => Real.exp (-c * |x|) := by
  have h0 : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.2 hc) 0).congr_fun
      (fun x hx => by simp [abs_of_pos (mem_Ioi.1 hx)]) measurableSet_Ioi
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  refine IntegrableOn.union ((integrableOn_exp_mul_Iic hc 0).congr_fun
    (fun x hx => by simp [abs_of_nonpos (mem_Iic.1 hx)]) measurableSet_Iic) h0

lemma pow_mul_exp_le (m : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C, ∀ x : ℝ, |x| ^ m * Real.exp (-c * |x|) ≤ C := by
  refine ⟨m.factorial / c ^ m, fun x => ?_⟩
  have h := Real.pow_div_factorial_le_exp (c * |x|) (by positivity) m
  rw [div_le_iff₀ (by positivity), mul_pow] at h
  rw [le_div_iff₀ (by positivity), neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_mul_eq_mul_div,
    div_le_iff₀ (Real.exp_pos _)]
  linarith

lemma integrable_pow_mul_exp (m : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable fun x : ℝ => |x| ^ m * Real.exp (-c * |x|) := by
  obtain ⟨C, hC⟩ := pow_mul_exp_le m (half_pos hc)
  refine ((integrable_exp_neg_mul_abs (half_pos hc)).const_mul C).mono'
    (by fun_prop) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity), show -c * |x| = -(c / 2) * |x| + -(c / 2) * |x| by ring,
    Real.exp_add, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hC x) (Real.exp_pos _).le

variable {f : 𝓢(ℝ, ℂ)}

lemma exists_decay (f : 𝓢(ℝ, ℂ)) (k : ℕ) : ∃ C, 0 ≤ C ∧ ∀ x : ℝ, |x| ^ k * ‖f x‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := f.decay k 0
  exact ⟨C, hC.le, fun x => by simpa using h x⟩

lemma exists_term_le (f : 𝓢(ℝ, ℂ)) (k : ℕ) : ∃ C, 0 ≤ C ∧ ∀ (x : ℝ) (n : ℕ),
    ‖f ((n + 1) * Real.exp x)‖ ≤ C * Real.exp (-(k + 2 : ℕ) * x) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
  obtain ⟨C, hC, h⟩ := exists_decay f (k + 2)
  refine ⟨C, hC, fun x n => ?_⟩
  have h1 := h ((n + 1) * Real.exp x)
  have hn : (1 : ℝ) ≤ n + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [abs_of_pos (by positivity), mul_pow, ← Real.exp_nat_mul] at h1
  have h2 : ((n : ℝ) + 1) ^ 2 ≤ (n + 1) ^ (k + 2) := pow_le_pow_right₀ hn (by omega)
  rw [neg_mul, Real.exp_neg, mul_one_div, ← div_eq_mul_inv, div_div, le_div_iff₀ (by positivity)]
  push_cast at h1 ⊢
  refine le_trans ?_ h1
  rw [mul_comm ‖_‖, mul_comm (Real.exp _)]
  gcongr

lemma summable_inv_sq : Summable fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2 :=
  (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)

lemma summable_theta (f : 𝓢(ℝ, ℂ)) (x : ℝ) : Summable fun n : ℕ => f ((n + 1) * Real.exp x) := by
  obtain ⟨C, _, h⟩ := exists_term_le f 0
  exact (summable_inv_sq.mul_left _).of_norm_bounded fun n => h x n

lemma exists_theta_le_of_nonneg (f : 𝓢(ℝ, ℂ)) (k : ℕ) : ∃ C, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x →
    ‖theta f x‖ ≤ C * Real.exp (-k * x) := by
  obtain ⟨C, hC, h⟩ := exists_term_le f k
  set S := ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ 2
  have hS : 0 ≤ S := tsum_nonneg fun n => by positivity
  refine ⟨C * S, by positivity, fun x hx => ?_⟩
  have h1 : ‖∑' n : ℕ, f ((n + 1) * Real.exp x)‖ ≤ C * Real.exp (-(k + 2 : ℕ) * x) * S :=
    tsum_of_norm_bounded (summable_inv_sq.hasSum.mul_left _) fun n => h x n
  rw [theta, norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h2 : Real.exp (x / 2) * Real.exp (-(k + 2 : ℕ) * x) ≤ Real.exp (-k * x) := by
    rw [← Real.exp_add, Real.exp_le_exp]; push_cast; linarith
  calc _ ≤ Real.exp (x / 2) * (C * Real.exp (-(k + 2 : ℕ) * x) * S) := by gcongr
    _ = C * S * (Real.exp (x / 2) * Real.exp (-(k + 2 : ℕ) * x)) := by ring
    _ ≤ _ := by gcongr

lemma measurable_theta (f : 𝓢(ℝ, ℂ)) : Measurable (theta f) := by
  refine Measurable.mul (by fun_prop) (measurable_of_tendsto_metrizable
    (f := fun N x => ∑ n ∈ Finset.range N, f ((n + 1) * Real.exp x))
    (fun N => ?_) (tendsto_pi_nhds.2 fun x => (summable_theta f x).hasSum.tendsto_sum_nat))
  have := f.continuous
  exact (by fun_prop : Continuous _).measurable

/-- The dilation `x ↦ f (r x)`. -/
noncomputable def dilate (r : ℝ) (hr : 0 < r) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 r hr.ne')) f

@[simp] lemma dilate_apply (r : ℝ) (hr : 0 < r) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dilate r hr f x = f (r * x) := by
  simp [dilate, mul_comm]

lemma fourier_dilate (r : ℝ) (hr : 0 < r) (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (dilate r hr f) ξ = (r⁻¹ : ℝ) * 𝓕 f (r⁻¹ * ξ) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  have h := Measure.integral_comp_mul_left
    (fun v : ℝ => cexp (↑(-2 * Real.pi * v * (r⁻¹ * ξ)) * I) • f v) r
  rw [abs_of_pos (inv_pos.2 hr), real_smul] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [dilate_apply]
  congr 4
  field_simp

lemma ThetaClass.fourier (hf : ThetaClass f) : ThetaClass (𝓕 f) where
  even ξ := by
    rw [SchwartzMap.fourier_coe, ← Real.fourierInv_eq_fourier_neg,
      Real.fourierInv_eq_fourier_comp_neg]
    simp [hf.even]
  zero := by
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
    simpa using hf.integral
  integral := by
    have h : 𝓕⁻ (𝓕 f) 0 = f 0 := by simp
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at h
    simpa [hf.zero] using h

lemma tsum_int_dilate (hf : ThetaClass f) (x : ℝ) :
    ∑' n : ℤ, f (Real.exp x * n) = 2 * ∑' n : ℕ, f ((n + 1) * Real.exp x) := by
  have h1 := summable_theta f x
  have h2 : ∀ n : ℕ, f (Real.exp x * ((n + 1 : ℕ) : ℤ)) = f ((n + 1) * Real.exp x) := fun n => by
    push_cast; rw [mul_comm]
  have h3 : ∀ n : ℕ, f (Real.exp x * (-((n : ℤ) + 1) : ℤ)) = f ((n + 1) * Real.exp x) := fun n => by
    rw [← hf.even]; push_cast; congr 1; ring
  rw [tsum_of_nat_of_neg_add_one ((summable_nat_add_iff 1).1 (by simpa only [h2] using h1))
    (by simpa only [h3] using h1)]
  rw [((summable_nat_add_iff 1).1 (by simpa only [h2] using h1) :
    Summable fun n : ℕ => f (Real.exp x * (n : ℤ))).tsum_eq_zero_add]
  simp only [h2, h3]
  simp [hf.zero, two_mul]

/-- **Poisson summation.** The Fourier transform reflects theta functions. -/
lemma theta_fourier (hf : ThetaClass f) (x : ℝ) : theta (𝓕 f) x = theta f (-x) := by
  have h := (dilate (Real.exp (-x)) (Real.exp_pos _) f).tsum_eq_tsum_fourier 0
  simp only [zero_add, dilate_apply, fourier_dilate, ← Real.exp_neg, neg_neg] at h
  simp only [QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one, tsum_mul_left] at h
  rw [tsum_int_dilate hf, tsum_int_dilate hf.fourier] at h
  have h' : ∑' n : ℕ, f ((n + 1) * Real.exp (-x)) =
      (Real.exp x : ℂ) * ∑' n : ℕ, 𝓕 f ((n + 1) * Real.exp x) := by
    linear_combination h / 2
  rw [theta, theta, h', ← mul_assoc, ← ofReal_mul, ← Real.exp_add]
  congr 3
  ring

lemma exists_theta_le (hf : ThetaClass f) (k : ℕ) : ∃ C, 0 ≤ C ∧ ∀ x : ℝ,
    ‖theta f x‖ ≤ C * Real.exp (-k * |x|) := by
  obtain ⟨C, hC, h⟩ := exists_theta_le_of_nonneg f k
  obtain ⟨D, hD, h'⟩ := exists_theta_le_of_nonneg (𝓕 f) k
  refine ⟨C + D, by positivity, fun x => ?_⟩
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    refine (h x hx).trans ?_
    gcongr
    linarith
  · rw [abs_of_nonpos hx, ← neg_neg x, ← theta_fourier hf, neg_neg]
    refine (h' (-x) (by linarith)).trans ?_
    gcongr
    linarith

/-! ### Moments of theta functions -/

/-- The moment `∫ u(x) x^m e^{zx} dx`. -/
noncomputable def jet (u : ℝ → ℂ) (m : ℕ) (z : ℂ) : ℂ := ∫ x : ℝ, u x * ((x : ℂ) ^ m * exp (z * x))

lemma norm_pow_mul_exp (m : ℕ) (z : ℂ) (x : ℝ) :
    ‖(x : ℂ) ^ m * exp (z * x)‖ = |x| ^ m * Real.exp (z.re * x) := by
  rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, norm_exp]
  simp

lemma re_mul_le {z : ℂ} {b : ℝ} (hz : |z.re| ≤ b) (x : ℝ) : z.re * x ≤ b * |x| := by
  calc z.re * x ≤ |z.re * x| := le_abs_self _
    _ = |z.re| * |x| := abs_mul _ _
    _ ≤ _ := by gcongr

lemma exists_integrand_le (hf : ThetaClass f) (m : ℕ) (b : ℝ) : ∃ C, ∀ z : ℂ, |z.re| ≤ b → ∀ x : ℝ,
    ‖theta f x * ((x : ℂ) ^ m * exp (z * x))‖ ≤ C * (|x| ^ m * Real.exp (-1 * |x|)) := by
  obtain ⟨C, hC, h⟩ := exists_theta_le hf (⌈b⌉₊ + 1)
  refine ⟨C, fun z hz x => ?_⟩
  rw [norm_mul, norm_pow_mul_exp]
  have h1 := h x
  have h2 : Real.exp (-(⌈b⌉₊ + 1 : ℕ) * |x|) * Real.exp (z.re * x) ≤ Real.exp (-1 * |x|) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have := re_mul_le hz x
    have := mul_le_mul_of_nonneg_right (Nat.le_ceil b) (abs_nonneg x)
    push_cast
    linarith
  calc _ ≤ C * Real.exp (-(⌈b⌉₊ + 1 : ℕ) * |x|) * (|x| ^ m * Real.exp (z.re * x)) := by gcongr
    _ = C * (|x| ^ m * (Real.exp (-(⌈b⌉₊ + 1 : ℕ) * |x|) * Real.exp (z.re * x))) := by ring
    _ ≤ _ := by gcongr

lemma aestronglyMeasurable_integrand (f : 𝓢(ℝ, ℂ)) (m : ℕ) (z : ℂ) :
    AEStronglyMeasurable (fun x : ℝ => theta f x * ((x : ℂ) ^ m * exp (z * x))) := by
  have := measurable_theta f
  exact (by fun_prop : Measurable _).aestronglyMeasurable

lemma integrable_integrand (hf : ThetaClass f) (m : ℕ) (z : ℂ) :
    Integrable fun x : ℝ => theta f x * ((x : ℂ) ^ m * exp (z * x)) := by
  obtain ⟨C, hC⟩ := exists_integrand_le hf m |z.re|
  exact ((integrable_pow_mul_exp m one_pos).const_mul C).mono'
    (aestronglyMeasurable_integrand f m z) (Eventually.of_forall (hC z le_rfl))

lemma hasDerivAt_jet (hf : ThetaClass f) (m : ℕ) (z : ℂ) :
    HasDerivAt (jet (theta f) m) (jet (theta f) (m + 1) z) z := by
  obtain ⟨C, hC⟩ := exists_integrand_le hf (m + 1) (|z.re| + 1)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z one_pos)
    (Eventually.of_forall (aestronglyMeasurable_integrand f m)) (integrable_integrand hf m z)
    (aestronglyMeasurable_integrand f (m + 1) z) (Eventually.of_forall fun x w hw => hC w ?_ x)
    ((integrable_pow_mul_exp (m + 1) one_pos).const_mul C)
    (Eventually.of_forall fun x w _ => ?_)).2
  · have h1 := (abs_re_le_norm (w - z)).trans (mem_ball_iff_norm.1 hw).le
    have h2 := abs_add_le (w - z).re z.re
    rw [← add_re, sub_add_cancel] at h2
    linarith
  · have h := (((hasDerivAt_id w).mul_const (x : ℂ)).cexp.const_mul ((x : ℂ) ^ m)).const_mul
      (theta f x)
    refine h.congr_deriv ?_
    simp only [id, pow_succ]
    ring

lemma differentiable_jet (hf : ThetaClass f) (m : ℕ) : Differentiable ℂ (jet (theta f) m) :=
  fun z => (hasDerivAt_jet hf m z).differentiableAt

lemma iteratedDeriv_jet (hf : ThetaClass f) (m : ℕ) :
    iteratedDeriv m (jet (theta f) 0) = jet (theta f) m := by
  induction m with
  | zero => simp
  | succ m ih => rw [iteratedDeriv_succ, ih]; exact funext fun z => (hasDerivAt_jet hf m z).deriv

lemma mellin_eq_integral (h : ℝ → ℂ) (s : ℂ) :
    mellin h s = ∫ x : ℝ, h (Real.exp x) * exp (s * x) := by
  rw [mellin_eq_fourier, Real.fourier_eq', ← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have hin : inner ℝ (-u) (s.im / (2 * Real.pi)) = s.im / (2 * Real.pi) * -u := rfl
  simp only [neg_neg, smul_eq_mul, real_smul, hin]
  rw [ofReal_exp, ← mul_assoc, ← Complex.exp_add, mul_comm]
  congr 2
  have h2 : (Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  conv_rhs => rw [← re_add_im s]
  push_cast
  field_simp
  ring

lemma integrable_mellin (f : 𝓢(ℝ, ℂ)) {s : ℂ} (hs : 0 < s.re) :
    Integrable fun x : ℝ => f (Real.exp x) * exp (s * x) := by
  obtain ⟨C, hC, h⟩ := exists_decay f 0
  obtain ⟨D, hD, h'⟩ := exists_decay f (⌈s.re⌉₊ + 1)
  have hf := f.continuous
  refine ((integrable_exp_neg_mul_abs (lt_min hs one_pos)).const_mul (C + D)).mono'
    (by fun_prop : Continuous _).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_exp, show (s * x).re = s.re * x by simp]
  rcases le_total x 0 with hx | hx
  · have h1 := h (Real.exp x)
    rw [pow_zero, one_mul] at h1
    have h2 := mul_le_mul_of_nonpos_right (min_le_left s.re 1) hx
    rw [abs_of_nonpos hx]
    exact mul_le_mul (by linarith) (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le
      (by positivity)
  · have h1 := h' (Real.exp x)
    rw [abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul] at h1
    have h2 : Real.exp (s.re * x) ≤
        Real.exp ((⌈s.re⌉₊ + 1 : ℕ) * x) * Real.exp (-min s.re 1 * |x|) := by
      rw [← Real.exp_add, Real.exp_le_exp, abs_of_nonneg hx]
      have := mul_le_mul_of_nonneg_right (min_le_right s.re 1) hx
      have := mul_le_mul_of_nonneg_right (Nat.le_ceil s.re) hx
      push_cast
      linarith
    calc _ ≤ ‖f (Real.exp x)‖ * (Real.exp ((⌈s.re⌉₊ + 1 : ℕ) * x) *
          Real.exp (-min s.re 1 * |x|)) := by gcongr
      _ = Real.exp ((⌈s.re⌉₊ + 1 : ℕ) * x) * ‖f (Real.exp x)‖ *
          Real.exp (-min s.re 1 * |x|) := by ring
      _ ≤ _ := by gcongr; linarith

lemma differentiableAt_mellin (f : 𝓢(ℝ, ℂ)) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin f) s := by
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := 0)
    (f.continuous.locallyIntegrable.locallyIntegrableOn _) ?_ (by linarith) ?_ hs
  · refine ((f.isBigO_cocompact_rpow (-(s.re + 1))).mono atTop_le_cocompact).congr' .rfl ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.norm_of_nonneg hx.le]
  · simp only [neg_zero, Real.rpow_zero]
    exact (f.continuous.tendsto 0).isBigO_one ℝ |>.mono nhdsWithin_le_nhds

/-- In the half-plane of absolute convergence, the moment is a Dirichlet series. -/
lemma jet_theta_of_one_lt (f : 𝓢(ℝ, ℂ)) {s : ℂ} (hs : 1 < s.re) :
    jet (theta f) 0 (s - 1 / 2) = riemannZeta s * mellin f s := by
  set G : ℝ → ℂ := fun x => f (Real.exp x) * exp (s * x) with hG
  have hGi : Integrable G := integrable_mellin f (by linarith)
  set F : ℕ → ℝ → ℂ := fun n x => f ((n + 1) * Real.exp x) * exp (s * x)
  have hF : ∀ n x, F n x = exp (-s * Real.log (n + 1)) * G (x + Real.log (n + 1)) := by
    intro n x
    have hn : (0 : ℝ) < n + 1 := by positivity
    simp only [F, hG]
    rw [Real.exp_add, Real.exp_log hn, mul_left_comm, ← Complex.exp_add, mul_comm (Real.exp x)]
    congr 2
    push_cast
    ring
  have hnorm : ∀ n : ℕ, ‖exp (-s * Real.log (n + 1))‖ = 1 / ((n + 1 : ℕ) : ℝ) ^ s.re := by
    intro n
    have hn : (0 : ℝ) < n + 1 := by positivity
    rw [norm_exp, show (-s * (Real.log (n + 1) : ℝ)).re = Real.log (n + 1) * (-s.re) by
      rw [re_mul_ofReal, neg_re, mul_comm], ← Real.rpow_def_of_pos hn, Real.rpow_neg hn.le]
    simp
  have h := hasSum_integral_of_summable_integral_norm (F := F) (μ := volume)
    (fun n => by
      rw [funext (hF n)]
      exact (hGi.comp_add_right _).const_mul _) (by
      have e : ∀ n : ℕ, ∫ x, ‖F n x‖ = 1 / ((n + 1 : ℕ) : ℝ) ^ s.re * ∫ x, ‖G x‖ := fun n => by
        rw [← integral_add_right_eq_self (fun x => ‖G x‖) (Real.log (n + 1)), ← integral_const_mul]
        simp only [hF, norm_mul, hnorm]
      simp only [e]
      exact ((summable_nat_add_iff 1).2 (Real.summable_one_div_nat_rpow.2 hs)).mul_right _)
  have e : jet (theta f) 0 (s - 1 / 2) = ∫ x, ∑' n, F n x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [F, theta, tsum_mul_right, pow_zero, one_mul]
    rw [ofReal_exp]
    rw [mul_right_comm, mul_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, ← h.tsum_eq, zeta_eq_tsum_one_div_nat_add_one_cpow hs, ← tsum_mul_right]
  refine tsum_congr fun n => ?_
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  simp only [hF, integral_const_mul]
  rw [integral_add_right_eq_self G, mellin_eq_integral]
  rw [one_div, ← cpow_neg, cpow_def_of_ne_zero hn, mul_comm (-s)]
  congr 3
  rw [ofReal_log (by positivity)]
  push_cast
  rfl

/-- `(s - 1) ζ(s)`, continued to the pole. -/
noncomputable def zetaNum : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1

lemma zetaNum_of_ne {s : ℂ} (hs : s ≠ 1) : zetaNum s = (s - 1) * riemannZeta s :=
  Function.update_of_ne hs _ _

lemma differentiable_zetaNum : Differentiable ℂ zetaNum := by
  intro s
  have h : ∀ w : ℂ, w ≠ 1 → DifferentiableAt ℂ zetaNum w := fun w hw =>
    ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hw)).congr_of_eventuallyEq
      ((eventually_ne_nhds hw).mono fun _ h => zetaNum_of_ne h)
  rcases eq_or_ne s 1 with rfl | hs
  · refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_
      (continuousAt_update_same.2 riemannZeta_residue_one)).differentiableAt
    filter_upwards [self_mem_nhdsWithin] using h
  · exact h s hs

lemma sub_one_mul_jet (hf : ThetaClass f) {s : ℂ} (hs : 0 < s.re) :
    (s - 1) * jet (theta f) 0 (s - 1 / 2) = zetaNum s * mellin f s := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have h1 : AnalyticOnNhd ℂ (fun s => (s - 1) * jet (theta f) 0 (s - 1 / 2)) {s | 0 < s.re} :=
    DifferentiableOn.analyticOnNhd (fun s _ => by
      have := differentiable_jet hf 0
      exact (by fun_prop : DifferentiableAt ℂ _ s).differentiableWithinAt) hU
  have h2 : AnalyticOnNhd ℂ (fun s => zetaNum s * mellin f s) {s | 0 < s.re} :=
    DifferentiableOn.analyticOnNhd (fun s hs =>
      ((differentiable_zetaNum s).mul (differentiableAt_mellin f hs)).differentiableWithinAt) hU
  refine h1.eqOn_of_preconnected_of_eventuallyEq h2 (convex_halfSpace_re_gt 0).isPreconnected
    (z₀ := 2) (by simp) ?_ hs
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
    (show (1 : ℝ) < (2 : ℂ).re by simp)] with w hw
  have hw1 : w ≠ 1 := by rintro rfl; simp at hw
  rw [zetaNum_of_ne hw1, jet_theta_of_one_lt f hw, mul_assoc]

/-- **Mellin transform of a theta function**, up to the line `Re z = -1/2`. The point `z = 1/2` is
excluded because `ζ` has its pole there. -/
theorem integral_theta (hf : ThetaClass f) {z : ℂ} (hz : -1 / 2 < z.re) (hz' : z ≠ 1 / 2) :
    ∫ x : ℝ, theta f x * exp (z * x) = riemannZeta (1 / 2 + z) * mellin f (1 / 2 + z) := by
  have hs : 1 / 2 + z - 1 ≠ 0 := fun h => hz' (by linear_combination h)
  have h := sub_one_mul_jet hf (s := 1 / 2 + z) (by norm_num; linarith)
  rw [zetaNum_of_ne (sub_ne_zero.1 hs), mul_assoc] at h
  have h' := mul_left_cancel₀ hs h
  rw [add_sub_cancel_left] at h'
  simpa [jet] using h'

/-! ### Prescribed orders of vanishing -/

lemma mellin_dilate {r : ℝ} (hr : 0 < r) (f : 𝓢(ℝ, ℂ)) (s : ℂ) :
    mellin (dilate r hr f) s = exp (-s * Real.log r) * mellin f s := by
  have : (dilate r hr f : ℝ → ℂ) = fun t => f (r * t) := funext (dilate_apply r hr f)
  rw [this, mellin_comp_mul_left _ _ hr, smul_eq_mul,
    cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), ofReal_log hr.le, mul_comm (log _)]

/-- `f - r^c f(r ·)`. -/
noncomputable def sharpen (r : ℝ) (hr : 0 < r) (c : ℂ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  f - exp (c * Real.log r) • dilate r hr f

lemma sharpen_apply (r : ℝ) (hr : 0 < r) (c : ℂ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    sharpen r hr c f x = f x - exp (c * Real.log r) * f (r * x) := by
  simp [sharpen]

lemma mellin_sharpen {r : ℝ} (hr : 0 < r) (c : ℂ) (f : 𝓢(ℝ, ℂ)) {s : ℂ} (hs : 0 < s.re) :
    mellin (sharpen r hr c f) s = (1 - exp ((c - s) * Real.log r)) * mellin f s := by
  have h1 := mellin_dilate hr f s
  simp only [mellin_eq_integral] at h1 ⊢
  simp only [sharpen_apply, sub_mul, mul_assoc]
  have h2 := integrable_mellin (dilate r hr f) hs
  simp only [dilate_apply] at h1 h2
  rw [integral_sub (integrable_mellin f hs) (h2.const_mul _), integral_const_mul, h1, ← mul_assoc,
    ← Complex.exp_add, one_mul]
  congr 3
  ring

lemma ThetaClass.sharpen (hf : ThetaClass f) {r : ℝ} (hr : 0 < r) (c : ℂ) :
    ThetaClass (sharpen r hr c f) where
  even x := by simp [sharpen_apply, hf.even]
  zero := by simp [sharpen_apply, hf.zero]
  integral := by
    simp only [sharpen_apply]
    have h := f.integrable (μ := volume)
    rw [integral_sub h ((h.comp_mul_left' hr.ne').const_mul _), integral_const_mul,
      Measure.integral_comp_mul_left, hf.integral]
    simp

lemma analyticAt_mellin (f : 𝓢(ℝ, ℂ)) {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ (mellin f) s := by
  refine DifferentiableOn.analyticAt (s := {s : ℂ | 0 < s.re})
    (fun w hw => (differentiableAt_mellin f hw).differentiableWithinAt)
    ((isOpen_lt continuous_const continuous_re).mem_nhds hs)

lemma analyticOrderAt_one_sub_exp {l : ℝ} (hl : l ≠ 0) (c : ℂ) :
    analyticOrderAt (fun s => 1 - exp ((c - s) * l)) c = 1 := by
  have hd : HasDerivAt (fun s => 1 - exp ((c - s) * l)) (l : ℂ) c := by
    have h := ((((hasDerivAt_id c).const_sub c).mul_const (l : ℂ)).cexp).const_sub 1
    simpa using h
  refine AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by fun_prop) (by simp) ?_
  rw [hd.deriv]
  exact_mod_cast hl

lemma analyticOrderAt_mellin_sharpen {r : ℝ} (hr : 0 < r) (c : ℂ) (f : 𝓢(ℝ, ℂ)) {s : ℂ}
    (hs : 0 < s.re) : analyticOrderAt (mellin (sharpen r hr c f)) s =
      analyticOrderAt (fun s => 1 - exp ((c - s) * Real.log r)) s +
        analyticOrderAt (mellin f) s := by
  rw [← analyticOrderAt_mul (by fun_prop) (analyticAt_mellin f hs)]
  refine analyticOrderAt_congr ?_
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with w hw
  exact mellin_sharpen hr c f hw

/-- An even Schwartz function vanishing at `0` with nonzero Mellin transform at `s`. -/
lemma exists_even_mellin_ne_zero (s : ℂ) :
    ∃ f : 𝓢(ℝ, ℂ), (∀ x, f (-x) = f x) ∧ f 0 = 0 ∧ mellin f s ≠ 0 := by
  obtain ⟨φ, hφ⟩ := TestFunction.exists_hat_ne_zero s
  have hz : ∀ t : ℝ, t ≤ 1 → φ.toFun t = 0 := fun t ht => image_eq_zero_of_notMem_tsupport
    fun h => absurd (mem_Ioi.1 (φ.tsupport_subset h)) (not_lt.2 ht)
  let g := φ.hasCompactSupport.toSchwartzMap φ.contDiff
  let f : 𝓢(ℝ, ℂ) := g +
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ (M := ℝ)) g
  have hf : ∀ x, f x = φ.toFun x + φ.toFun (-x) := fun x => rfl
  refine ⟨f, fun x => by rw [hf, hf, neg_neg, add_comm], by simp [hf, hz], ?_⟩
  have e : mellin f s = φ.hat s := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [hf, hz (-t) (by linarith [mem_Ioi.1 ht]), add_zero]
  rwa [e]

/-- The order of the Mellin transform at `s` can be any natural number, except that `∫ f = 0` forces
a zero at `s = 1`. -/
lemma exists_thetaClass_order {s : ℂ} (hs : 0 < s.re) (k : ℕ) : ∃ f : 𝓢(ℝ, ℂ), ThetaClass f ∧
    analyticOrderAt (mellin f) s = analyticOrderAt (fun w : ℂ => w - 1) s + k := by
  induction k with
  | succ k ih =>
    obtain ⟨f, hf, ho⟩ := ih
    have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    refine ⟨sharpen 2 two_pos s f, hf.sharpen _ _, ?_⟩
    rw [analyticOrderAt_mellin_sharpen _ _ _ hs, analyticOrderAt_one_sub_exp hl, ho]
    push_cast
    ring
  | zero =>
    obtain ⟨f, hev, h0, hM⟩ := exists_even_mellin_ne_zero s
    set l : ℝ := 1 / (1 + ‖1 - s‖)
    have hl : 0 < l := by positivity
    have hclass : ThetaClass (sharpen (Real.exp l) (Real.exp_pos _) 1 f) :=
      { even := fun x => by simp [sharpen_apply, hev]
        zero := by simp [sharpen_apply, h0]
        integral := by
          have h := f.integrable (μ := volume)
          simp only [sharpen_apply]
          rw [integral_sub h ((h.comp_mul_left' (Real.exp_pos l).ne').const_mul _),
            integral_const_mul, Measure.integral_comp_mul_left, abs_of_pos (by positivity),
            real_smul, ← mul_assoc, Real.log_exp, one_mul, ← ofReal_exp, ← ofReal_mul,
            mul_inv_cancel₀ (Real.exp_pos l).ne']
          simp }
    refine ⟨_, hclass, ?_⟩
    rw [analyticOrderAt_mellin_sharpen _ _ _ hs,
      (analyticAt_mellin f hs).analyticOrderAt_eq_zero.2 hM, Real.log_exp, Nat.cast_zero]
    congr 1
    rcases eq_or_ne s 1 with rfl | hs1
    · rw [analyticOrderAt_one_sub_exp hl.ne']
      exact (AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by fun_prop) (by simp)
        (by simp)).symm
    · rw [(by fun_prop : AnalyticAt ℂ (fun w : ℂ => w - 1) s).analyticOrderAt_eq_zero.2
        (sub_ne_zero.2 hs1), AnalyticAt.analyticOrderAt_eq_zero (by fun_prop)]
      intro h
      have hn : 0 < ‖1 - s‖ := norm_pos_iff.2 (sub_ne_zero.2 hs1.symm)
      obtain ⟨n, hn'⟩ := exp_eq_one_iff.1 (sub_eq_zero.1 h).symm
      have h1 : ‖(1 - s) * (l : ℂ)‖ < 1 := by
        rw [norm_mul, norm_real, Real.norm_of_nonneg hl.le, mul_one_div, div_lt_one (by positivity)]
        linarith
      have h2 : 0 < ‖(1 - s) * (l : ℂ)‖ := by
        rw [norm_mul, norm_real, Real.norm_of_nonneg hl.le]; positivity
      rw [hn'] at h1 h2
      have hn0 : n ≠ 0 := by rintro rfl; simp at h2
      have h3 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
      simp only [norm_mul, norm_intCast, norm_I, norm_ofNat, norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, mul_one] at h1
      nlinarith [Real.pi_gt_three]

lemma analyticOrderAt_jet (hf : ThetaClass f) {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt (fun w : ℂ => w - 1) s + analyticOrderAt (jet (theta f) 0) (s - 1 / 2) =
      analyticOrderAt zetaNum s + analyticOrderAt (mellin f) s := by
  have hj := differentiable_jet hf 0
  rw [← analyticOrderAt_mul (differentiable_zetaNum.analyticAt s) (analyticAt_mellin f hs)]
  have h1 : analyticOrderAt (jet (theta f) 0) (s - 1 / 2) =
      analyticOrderAt (fun w => jet (theta f) 0 (w - 1 / 2)) s :=
    (analyticOrderAt_comp_of_deriv_ne_zero (f := jet (theta f) 0) (g := fun w : ℂ => w - 1 / 2)
      (by fun_prop) (by simp)).symm
  rw [h1, ← analyticOrderAt_mul (g := fun w => jet (theta f) 0 (w - 1 / 2)) (by fun_prop)
    ((by fun_prop : Differentiable ℂ _).analyticAt s)]
  refine analyticOrderAt_congr ?_
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with w hw
  exact sub_one_mul_jet hf hw

lemma analyticOrderAt_sub_one_ne_top (s : ℂ) : analyticOrderAt (fun w : ℂ => w - 1) s ≠ ⊤ := by
  intro h
  have h1 := EventuallyEq.deriv_eq (f := fun _ => (0 : ℂ)) (analyticOrderAt_eq_top.1 h)
  simp at h1

lemma analyticOrderAt_zetaNum (s : ℂ) : analyticOrderAt zetaNum s = zeroMult s := by
  rcases eq_or_ne s 1 with rfl | hs
  · have h1 : zeroMult 1 = 0 := by
      by_contra h
      exact riemannZeta_one_ne_zero (apply_eq_zero_of_analyticOrderNatAt_ne_zero h)
    rw [h1, (differentiable_zetaNum.analyticAt 1).analyticOrderAt_eq_zero.2 (by simp [zetaNum])]
    rfl
  · have e : analyticOrderAt zetaNum s = analyticOrderAt riemannZeta s := by
      rw [analyticOrderAt_congr (g := (fun w : ℂ => w - 1) * riemannZeta)
        ((eventually_ne_nhds hs).mono fun w hw => zetaNum_of_ne hw),
        analyticOrderAt_mul (by fun_prop) (analyticOn_riemannZeta s hs),
        (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w - 1) s).analyticOrderAt_eq_zero.2
          (sub_ne_zero.2 hs), zero_add]
    have hne : analyticOrderAt zetaNum s ≠ ⊤ := fun h => by
      have h0 := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s
        fun w => differentiable_zetaNum.analyticAt w).1 h
      simpa [zetaNum] using congrFun h0 1
    rw [e] at hne ⊢
    exact (Nat.cast_analyticOrderNatAt hne).symm

/-- The moments at `z` annihilate all theta functions up to the order of the zero, `Re z > -1/2`. -/
lemma forall_jet_eq_zero_iff_of_re {z : ℂ} (hz : -1 / 2 < z.re) (m : ℕ) :
    (∀ f, ThetaClass f → jet (theta f) m z = 0) ↔ m < zeroMult (1 / 2 + z) := by
  have hs : 0 < (1 / 2 + z).re := by norm_num; linarith
  have hord : ∀ f (hf : ThetaClass f), analyticOrderAt (fun w : ℂ => w - 1) (1 / 2 + z) +
      analyticOrderAt (jet (theta f) 0) z =
      zeroMult (1 / 2 + z) + analyticOrderAt (mellin f) (1 / 2 + z) := fun f hf => by
    have h := analyticOrderAt_jet hf hs
    rwa [analyticOrderAt_zetaNum, add_sub_cancel_left] at h
  constructor
  · intro h
    by_contra hm
    obtain ⟨f, hf, ho⟩ := exists_thetaClass_order hs (m - zeroMult (1 / 2 + z))
    have h1 := hord f hf
    rw [ho, add_left_comm] at h1
    have h2 := WithTop.add_left_cancel (analyticOrderAt_sub_one_ne_top _) h1
    rw [← Nat.cast_add, Nat.add_sub_cancel' (not_lt.1 hm)] at h2
    have h3 := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
      ((differentiable_jet hf 0).analyticAt z)).1 h2
    rw [iteratedDeriv_jet hf] at h3
    exact h3.2 (h f hf)
  · intro hm f hf
    have hA := (differentiable_jet hf 0).analyticAt z
    rw [← iteratedDeriv_jet hf]
    refine (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (n := zeroMult (1 / 2 + z)) hA).1 ?_ m hm
    have h1 := hord f hf
    rcases eq_or_ne (1 / 2 + z) 1 with e | e
    · rw [e] at hm
      have : zeroMult 1 = 0 := by
        by_contra h
        exact riemannZeta_one_ne_zero (apply_eq_zero_of_analyticOrderNatAt_ne_zero h)
      omega
    · rw [(by fun_prop : AnalyticAt ℂ (fun w : ℂ => w - 1) (1 / 2 + z)).analyticOrderAt_eq_zero.2
        (sub_ne_zero.2 e), zero_add] at h1
      rw [h1]
      exact le_self_add

lemma jet_theta_fourier (hf : ThetaClass f) (m : ℕ) (z : ℂ) :
    jet (theta (𝓕 f)) m z = (-1) ^ m * jet (theta f) m (-z) := by
  rw [jet, jet, ← integral_neg_eq_self, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [theta_fourier hf, neg_neg, ofReal_neg, neg_mul, mul_neg]
  rw [neg_pow (x : ℂ) m]
  ring

lemma forall_jet_eq_zero_iff (z : ℂ) (m : ℕ) :
    (∀ f, ThetaClass f → jet (theta f) m z = 0) ↔
      m < zeroMult (1 / 2 + z) ∧ 1 / 2 + z ∈ stripZeros := by
  have key : ∀ w : ℂ, m < zeroMult w → 0 < w.re → w ∈ stripZeros := fun w hw h0 => by
    have hz : riemannZeta w = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero (Nat.ne_zero_of_lt hw)
    exact ⟨hz, h0, not_le.1 fun h => riemannZeta_ne_zero_of_one_le_re h hz⟩
  have hre : (1 / 2 + z).re = 1 / 2 + z.re := by norm_num
  rcases lt_or_ge (-1 / 2) z.re with hz | hz
  · rw [forall_jet_eq_zero_iff_of_re hz]
    exact ⟨fun h => ⟨h, key _ h (by rw [hre]; linarith)⟩, fun h => h.1⟩
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · have h1 : ∀ f, ThetaClass f → jet (theta f) m (-z) = 0 := fun f hf => by
        have h2 := jet_theta_fourier hf m z
        rw [h _ hf.fourier] at h2
        simpa using h2.symm
      rw [forall_jet_eq_zero_iff_of_re (by rw [neg_re]; linarith)] at h1
      have h3 := (key _ h1 (by norm_num; linarith)).2.2
      norm_num at h3
      linarith
    · have := h.2.2.1
      rw [hre] at this
      linarith

/-! ### The Hilbert space and its functionals -/

/-- The measure `2 cosh (2 a x) dx`. -/
noncomputable def wt (a : ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (2 * Real.cosh (2 * a * x))

/-- The weighted `L²` space, in the logarithmic variable. -/
noncomputable abbrev W (a : ℝ) := Lp ℂ 2 (wt a)

/-- The closed span of the theta functions. -/
noncomputable def V (a : ℝ) : Submodule ℂ (W a) :=
  (Submodule.span ℂ {u : W a | ∃ f, ThetaClass f ∧ u =ᵐ[wt a] theta f}).topologicalClosure

lemma exp_le_weight {a : ℝ} (x : ℝ) : Real.exp (2 * a * |x|) ≤ 2 * Real.cosh (2 * a * x) := by
  rw [Real.cosh_eq]
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · linarith [Real.exp_pos (-(2 * a * x))]
  · rw [mul_neg]; linarith [Real.exp_pos (2 * a * x)]

lemma weight_le {a : ℝ} (ha : 0 < a) (x : ℝ) :
    2 * Real.cosh (2 * a * x) ≤ 2 * Real.exp (2 * a * |x|) := by
  have h1 : Real.exp (2 * a * x) ≤ Real.exp (2 * a * |x|) := by gcongr; exact le_abs_self x
  have h2 : Real.exp (-(2 * a * x)) ≤ Real.exp (2 * a * |x|) := by
    rw [← mul_neg]; gcongr; exact neg_le_abs x
  rw [Real.cosh_eq]
  linarith

lemma integral_wt (a : ℝ) (g : ℝ → ℂ) :
    ∫ x, g x ∂wt a = ∫ x, ((2 * Real.cosh (2 * a * x) : ℝ) : ℂ) * g x := by
  rw [wt, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * Real.cosh (2 * a * x)), real_smul]

lemma ae_wt_iff {a : ℝ} {p : ℝ → Prop} : (∀ᵐ x ∂wt a, p x) ↔ ∀ᵐ x, p x := by
  rw [wt, ae_withDensity_iff (by fun_prop)]
  refine eventually_congr (Eventually.of_forall fun x => ?_)
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact ⟨fun h => h (by positivity), fun h _ => h⟩

lemma memLp_wt {a : ℝ} {g : ℝ → ℂ} (hg : AEStronglyMeasurable g) {b : ℝ → ℝ} (hb : Integrable b)
    (h : ∀ x, 2 * Real.cosh (2 * a * x) * ‖g x‖ ^ 2 ≤ b x) : MemLp g 2 (wt a) := by
  have hg' : AEStronglyMeasurable g (wt a) := hg.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [memLp_two_iff_integrable_sq_norm hg', wt,
    integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine hb.mono' (((by fun_prop : Measurable fun x => ENNReal.ofReal
    (2 * Real.cosh (2 * a * x))).ennreal_toReal.aestronglyMeasurable).smul (hg.norm.pow 2))
    (Eventually.of_forall fun x => ?_)
  rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul, Real.norm_of_nonneg (by positivity)]
  exact h x

/-- Every theta function lies in every `W a`. -/
lemma memLp_theta {a : ℝ} (ha : 0 < a) (hf : ThetaClass f) : MemLp (theta f) 2 (wt a) := by
  obtain ⟨C, hC, h⟩ := exists_theta_le hf (⌈a⌉₊ + 1)
  refine memLp_wt (measurable_theta f).aestronglyMeasurable
    ((integrable_exp_neg_mul_abs two_pos).const_mul (2 * C ^ 2)) fun x => ?_
  have h1 : ‖theta f x‖ ^ 2 ≤ (C * Real.exp (-(⌈a⌉₊ + 1 : ℕ) * |x|)) ^ 2 := by gcongr; exact h x
  have h2 : Real.exp (2 * a * |x|) * Real.exp (-(⌈a⌉₊ + 1 : ℕ) * |x|) ^ 2 ≤
      Real.exp (-2 * |x|) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
    have := mul_le_mul_of_nonneg_right (Nat.le_ceil a) (abs_nonneg x)
    push_cast
    linarith
  calc _ ≤ 2 * Real.exp (2 * a * |x|) * (C * Real.exp (-(⌈a⌉₊ + 1 : ℕ) * |x|)) ^ 2 := by
        exact mul_le_mul (weight_le ha x) h1 (by positivity) (by positivity)
    _ = 2 * C ^ 2 * (Real.exp (2 * a * |x|) * Real.exp (-(⌈a⌉₊ + 1 : ℕ) * |x|) ^ 2) := by ring
    _ ≤ _ := by gcongr

/-- The Riesz representative of a moment. -/
noncomputable def kernel (a : ℝ) (m : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  conj ((x : ℂ) ^ m * exp (z * x)) / ((2 * Real.cosh (2 * a * x) : ℝ) : ℂ)

lemma memLp_kernel {a : ℝ} {z : ℂ} (hz : |z.re| < a) (m : ℕ) : MemLp (kernel a m z) 2 (wt a) := by
  have hc : 0 < 2 * (a - |z.re|) := by linarith
  have hpos : ∀ x : ℝ, 0 < 2 * Real.cosh (2 * a * x) := fun x => by positivity
  refine memLp_wt (Measurable.aestronglyMeasurable ?_) (integrable_pow_mul_exp (2 * m) hc)
    fun x => ?_
  · have : Measurable fun z : ℂ => conj z := continuous_conj.measurable
    exact (this.comp (by fun_prop)).div (by fun_prop)
  rw [kernel, norm_div, RCLike.norm_conj, norm_pow_mul_exp, norm_real,
    Real.norm_of_nonneg (hpos x).le, div_pow, mul_div_assoc', sq (2 * Real.cosh _),
    mul_div_mul_left _ _ (hpos x).ne', div_le_iff₀ (hpos x), mul_pow, ← pow_mul, mul_comm m,
    mul_assoc, ← Real.exp_nat_mul]
  have h1 : Real.exp ((2 : ℕ) * (z.re * x)) ≤
      Real.exp (-(2 * (a - |z.re|)) * |x|) * Real.exp (2 * a * |x|) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have := re_mul_le (le_refl |z.re|) x
    push_cast
    linarith
  gcongr
  exact h1.trans (by gcongr; exact exp_le_weight x)

/-- The moment as a continuous functional on `W a`. -/
noncomputable def moment {a : ℝ} {z : ℂ} (hz : |z.re| < a) (m : ℕ) : W a →L[ℂ] ℂ :=
  innerSL ℂ ((memLp_kernel hz m).toLp _)

lemma moment_apply {a : ℝ} {z : ℂ} (hz : |z.re| < a) (m : ℕ) (u : W a) :
    moment hz m u = ∫ x : ℝ, u x * ((x : ℂ) ^ m * exp (z * x)) := by
  rw [moment, innerSL_apply_apply, L2.inner_def, integral_wt]
  refine integral_congr_ae ?_
  filter_upwards [ae_wt_iff.1 (memLp_kernel hz m).coeFn_toLp] with x hx
  have hpos : ((2 * Real.cosh (2 * a * x) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (by positivity)
  rw [hx, RCLike.inner_apply, kernel, map_div₀, conj_conj, conj_ofReal]
  field_simp

/-- No moment is the zero functional. -/
lemma moment_ne_zero {a : ℝ} {z : ℂ} (hz : |z.re| < a) (m : ℕ) : moment hz m ≠ 0 := by
  intro h
  have h1 : (memLp_kernel hz m).toLp _ = 0 := by
    have h2 := congrArg (fun L => L ((memLp_kernel hz m).toLp _)) h
    rw [moment, innerSL_apply_apply] at h2
    exact inner_self_eq_zero.1 h2
  rw [Lp.eq_zero_iff_ae_eq_zero] at h1
  have h3 := ae_wt_iff.1 ((memLp_kernel hz m).coeFn_toLp.symm.trans h1)
  have h4 : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff]
  obtain ⟨x, hx, hx0⟩ := (h3.and h4).exists
  have hpos : (0 : ℝ) < 2 * Real.cosh (2 * a * x) := by positivity
  have hx' : kernel a m z x = 0 := hx
  rw [kernel, div_eq_zero_iff, map_eq_zero, mul_eq_zero] at hx'
  rcases hx' with (h5 | h5) | h5
  · exact hx0 (by exact_mod_cast eq_zero_of_pow_eq_zero h5)
  · exact exp_ne_zero _ h5
  · exact hpos.ne' (by exact_mod_cast h5)

lemma moment_vanishes_iff_jet {a : ℝ} {z : ℂ} (hz : |z.re| < a) (m : ℕ) :
    (∀ u ∈ V a, moment hz m u = 0) ↔ ∀ f, ThetaClass f → jet (theta f) m z = 0 := by
  have hjet : ∀ (u : W a) f, u =ᵐ[wt a] theta f → moment hz m u = jet (theta f) m z := by
    intro u f hu
    rw [moment_apply, jet]
    refine integral_congr_ae ?_
    filter_upwards [ae_wt_iff.1 hu] with x hx
    rw [hx]
  constructor
  · intro h f hf
    have hmem := memLp_theta ((abs_nonneg _).trans_lt hz) hf
    rw [← hjet (hmem.toLp _) f hmem.coeFn_toLp]
    exact h _ (Submodule.le_topologicalClosure _ (Submodule.subset_span
      ⟨f, hf, hmem.coeFn_toLp⟩))
  · intro h u hu
    have hle : V a ≤ LinearMap.ker (moment hz m).toLinearMap := by
      refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
        (moment hz m).isClosed_ker
      rintro v ⟨f, hf, hv⟩
      exact (hjet v f hv).trans (h f hf)
    exact hle hu

/-! ### The spectrum -/

/-- **Theorem S.** For `|Re z| < a` the `m`-th moment at `z` annihilates `V a` iff `1/2 + z` is a
zero of `ζ` in the critical strip, of multiplicity greater than `m`. -/
theorem moment_vanishes_iff {a : ℝ} {z : ℂ} (hz : |z.re| < a) (m : ℕ) :
    (∀ u ∈ V a, moment hz m u = 0) ↔
      1 / 2 + z ∈ innerZeros a ∧ m < zeroMult (1 / 2 + z) := by
  rw [moment_vanishes_iff_jet, forall_jet_eq_zero_iff, and_comm]
  refine and_congr_left fun _ => ⟨fun h => ⟨h.1, h.2.1, h.2.2, ?_⟩, fun h => ⟨h.1, h.2.1, h.2.2.1⟩⟩
  simpa using hz

/-- For `a ≤ 1/2` the strip condition is automatic. -/
theorem moment_vanishes_iff_of_le_half {a : ℝ} (ha : a ≤ 1 / 2) {z : ℂ} (hz : |z.re| < a) (m : ℕ) :
    (∀ u ∈ V a, moment hz m u = 0) ↔ m < zeroMult (1 / 2 + z) := by
  rw [moment_vanishes_iff_jet, forall_jet_eq_zero_iff_of_re]
  linarith [(abs_lt.1 hz).1]

/-- The characters that annihilate `V a` are the zeros at distance less than `a` from the critical
line. -/
theorem moment_zero_vanishes_iff {a : ℝ} {z : ℂ} (hz : |z.re| < a) :
    (∀ u ∈ V a, moment hz 0 u = 0) ↔ 1 / 2 + z ∈ innerZeros a := by
  rw [moment_vanishes_iff]
  exact and_iff_left_of_imp fun h => zeroMult_pos h.1

lemma abs_re_lt_of_mem {a : ℝ} {ρ : ℂ} (h : ρ ∈ innerZeros a) : |(ρ - 1 / 2).re| < a := by
  simpa using h.2.2.2

/-- A zero at distance less than `a` from the critical line makes the quotient nonzero. -/
theorem V_ne_top {a : ℝ} {ρ : ℂ} (h : ρ ∈ innerZeros a) : V a ≠ ⊤ := by
  intro e
  refine moment_ne_zero (abs_re_lt_of_mem h) 0 (ContinuousLinearMap.ext fun u => ?_)
  exact (moment_zero_vanishes_iff (abs_re_lt_of_mem h)).2 (by simpa using h) u (by simp [e])

/-! ### Negative controls -/

/-- The bound on `m` is sharp: at a zero, the moment whose index is the multiplicity does not
annihilate `V a`. -/
theorem moment_zeroMult_not_vanishing {a : ℝ} {ρ : ℂ} (h : ρ ∈ innerZeros a) :
    ¬ ∀ u ∈ V a, moment (abs_re_lt_of_mem h) (zeroMult ρ) u = 0 := by
  rw [moment_vanishes_iff]
  simp

/-- The strip condition in `moment_vanishes_iff` cannot be dropped: at the trivial zero `-2` the
multiplicity is positive, yet the character does not annihilate `V 3`. -/
theorem trivial_zero_not_vanishing : ∃ (z : ℂ) (hz : |z.re| < 3),
    0 < zeroMult (1 / 2 + z) ∧ ¬ ∀ u ∈ V 3, moment hz 0 u = 0 := by
  refine ⟨-5 / 2, by norm_num [abs_lt], ?_, ?_⟩
  · rw [show (1 / 2 + -5 / 2 : ℂ) = -2 * ((0 : ℕ) + 1) by norm_num]
    exact zeroMult_pos (riemannZeta_neg_two_mul_nat_add_one 0)
  · rw [moment_zero_vanishes_iff]
    intro h
    have := h.2.1
    norm_num at this

end Masullo.Spectrum
