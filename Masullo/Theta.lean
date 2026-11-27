import Masullo.Strength
import Masullo.Synthesis.Duality

/-!
# Theta functions

The theta function of an even Schwartz function `f` with `f 0 = ∫ f = 0`. Poisson summation gives
rapid decay at both ends, so its moments are entire in `z`. The identity of its transform with `ζ`
times a Mellin transform is the Dirichlet series for `Re z > 1/2` and extends to `Re z > -1/2` by
the identity theorem.

The theta functions and their Mellin transforms are those of Connes's and Meyer's spectral
realisations (recalled; the sources were not consulted).
-/

open MeasureTheory Complex Set Filter Topology
open scoped InnerProductSpace SchwartzMap FourierTransform ComplexConjugate ENNReal

namespace Masullo.Spectrum

open Synthesis

/-! ### Theta functions -/

/-- `x ↦ e^(x/2) ∑_{n ≥ 1} f(n e^x)`. -/
noncomputable def theta (f : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  Real.exp (x / 2) * ∑' n : ℕ, f ((n + 1) * Real.exp x)

/-- Even Schwartz functions with `f 0 = ∫ f = 0`. -/
structure ThetaClass (f : 𝓢(ℝ, ℂ)) : Prop where
  even : ∀ x, f (-x) = f x
  zero : f 0 = 0
  integral : ∫ x, f x = 0

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

lemma ThetaClass.rapid (hf : ThetaClass f) : Rapid (theta f) where
  aesm := (measurable_theta f).aestronglyMeasurable
  decay b := by
    obtain ⟨C, hC, h⟩ := exists_theta_le hf ⌈b⌉₊
    refine ⟨C, fun x => (h x).trans ?_⟩
    gcongr
    exact Nat.le_ceil b

/-! ### Moments of theta functions -/

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
noncomputable abbrev zetaNum : ℂ → ℂ := riemannZeta₁

lemma zetaNum_of_ne {s : ℂ} (hs : s ≠ 1) : zetaNum s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.2 hs), one_mul]

lemma differentiable_zetaNum : Differentiable ℂ zetaNum := differentiable_riemannZeta₁

lemma sub_one_mul_jet (hf : ThetaClass f) {s : ℂ} (hs : 0 < s.re) :
    (s - 1) * jet (theta f) 0 (s - 1 / 2) = zetaNum s * mellin f s := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have h1 : AnalyticOnNhd ℂ (fun s => (s - 1) * jet (theta f) 0 (s - 1 / 2)) {s | 0 < s.re} :=
    DifferentiableOn.analyticOnNhd (fun s _ => by
      have := hf.rapid.differentiable_jet
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

/-! ### Orders of vanishing -/

lemma analyticAt_mellin (f : 𝓢(ℝ, ℂ)) {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ (mellin f) s := by
  refine DifferentiableOn.analyticAt (s := {s : ℂ | 0 < s.re})
    (fun w hw => (differentiableAt_mellin f hw).differentiableWithinAt)
    ((isOpen_lt continuous_const continuous_re).mem_nhds hs)

lemma analyticOrderAt_jet (hf : ThetaClass f) {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt (fun w : ℂ => w - 1) s + analyticOrderAt (jet (theta f) 0) (s - 1 / 2) =
      analyticOrderAt zetaNum s + analyticOrderAt (mellin f) s := by
  have hj := hf.rapid.differentiable_jet
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
    exact e.trans (Nat.cast_analyticOrderNatAt (WeilExplicit.zeta_order_ne_top hs)).symm

end Masullo.Spectrum
