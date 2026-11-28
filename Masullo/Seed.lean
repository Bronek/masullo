import Masullo.Theta
import WeilExplicit.Completed

/-!
# The Riemann xi function as the transform of a theta function

The seed `f(x) = (4π²x⁴ - 6πx²) e^{-πx²}` is an even Schwartz function with `f 0 = ∫ f = 0`. Its
theta function has transform `ξ(1/2 + z)`, whose zeros are the zeros of zeta in the critical strip
with their multiplicities. The integral is Riemann's (recalled).
-/

open MeasureTheory Complex Set Filter Topology
open scoped InnerProductSpace SchwartzMap FourierTransform ComplexConjugate ENNReal

namespace Masullo.Synthesis

open Spectrum

/-- A polynomial times the Gaussian `e^{-πx²}`. -/
noncomputable def polyGauss (P : Polynomial ℂ) (x : ℝ) : ℂ :=
  P.eval (x : ℂ) * exp (-Real.pi * (x : ℂ) ^ 2)

lemma hasDerivAt_polyGauss (P : Polynomial ℂ) (x : ℝ) : HasDerivAt (polyGauss P)
    (polyGauss (P.derivative - Polynomial.C (2 * Real.pi : ℂ) * Polynomial.X * P) x) x := by
  have h1 : HasDerivAt (fun z : ℂ => P.eval z * exp (-Real.pi * z ^ 2)) _ (x : ℂ) :=
    (P.hasDerivAt _).mul ((((hasDerivAt_id (x : ℂ)).pow 2).const_mul (-Real.pi : ℂ)).cexp)
  refine h1.comp_ofReal.congr_deriv ?_
  simp [polyGauss]
  ring

lemma exists_iteratedDeriv_polyGauss (n : ℕ) (P : Polynomial ℂ) :
    ∃ Q, iteratedDeriv n (polyGauss P) = polyGauss Q := by
  induction n with
  | zero => exact ⟨P, by simp⟩
  | succ n ih =>
    obtain ⟨Q, hQ⟩ := ih
    rw [iteratedDeriv_succ, hQ]
    exact ⟨_, funext fun x => (hasDerivAt_polyGauss Q x).deriv⟩

lemma contDiff_polyGauss (P : Polynomial ℂ) : ContDiff ℝ (⊤ : ℕ∞) (polyGauss P) :=
  contDiff_of_differentiable_iteratedDeriv fun m _ => by
    obtain ⟨Q, hQ⟩ := exists_iteratedDeriv_polyGauss m P
    rw [hQ]
    exact fun x => (hasDerivAt_polyGauss Q x).differentiableAt

lemma polyGauss_decay (k : ℕ) (P : Polynomial ℂ) : ∃ C, ∀ x : ℝ, |x| ^ k * ‖polyGauss P x‖ ≤ C := by
  have hg : ∀ x : ℝ, ‖exp (-Real.pi * (x : ℂ) ^ 2)‖ ≤
      Real.exp Real.pi * Real.exp (-Real.pi * |x|) := fun x => by
    rw [norm_exp, ← Real.exp_add, Real.exp_le_exp,
      show (-(Real.pi : ℂ) * (x : ℂ) ^ 2).re = -Real.pi * |x| ^ 2 by
        rw [sq_abs, ← ofReal_neg, ← ofReal_pow, ← ofReal_mul, ofReal_re]]
    nlinarith [Real.pi_pos, sq_nonneg (|x| - 1), abs_nonneg x]
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨C, hC⟩ := hP
    obtain ⟨D, hD⟩ := hQ
    refine ⟨C + D, fun x => ?_⟩
    have e : polyGauss (P + Q) x = polyGauss P x + polyGauss Q x := by
      simp [polyGauss, add_mul]
    rw [e]
    calc _ ≤ |x| ^ k * (‖polyGauss P x‖ + ‖polyGauss Q x‖) := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by rw [mul_add]; exact add_le_add (hC x) (hD x)
  | monomial n c =>
    obtain ⟨C, hC⟩ := pow_mul_exp_le (k + n) Real.pi_pos
    refine ⟨‖c‖ * Real.exp Real.pi * C, fun x => ?_⟩
    rw [polyGauss, Polynomial.eval_monomial, norm_mul, norm_mul, norm_pow, norm_real,
      Real.norm_eq_abs]
    calc _ ≤ |x| ^ k * (‖c‖ * |x| ^ n * (Real.exp Real.pi * Real.exp (-Real.pi * |x|))) := by
          gcongr; exact hg x
      _ = ‖c‖ * Real.exp Real.pi * (|x| ^ (k + n) * Real.exp (-Real.pi * |x|)) := by
          rw [pow_add]; ring
      _ ≤ _ := by gcongr; exact hC x

open Polynomial in
/-- The seed `(4π²x⁴ - 6πx²) e^{-πx²}`. -/
noncomputable def seed : 𝓢(ℝ, ℂ) where
  toFun := polyGauss (C (4 * Real.pi ^ 2 : ℂ) * X ^ 4 - C (6 * Real.pi : ℂ) * X ^ 2)
  smooth' := contDiff_polyGauss _
  decay' k n := by
    obtain ⟨Q, hQ⟩ := exists_iteratedDeriv_polyGauss n
      (C (4 * Real.pi ^ 2 : ℂ) * X ^ 4 - C (6 * Real.pi : ℂ) * X ^ 2)
    obtain ⟨D, hD⟩ := polyGauss_decay k Q
    refine ⟨D, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hQ, Real.norm_eq_abs]
    exact hD x

lemma seed_apply (x : ℝ) : seed x =
    (4 * Real.pi ^ 2 * (x : ℂ) ^ 4 - 6 * Real.pi * (x : ℂ) ^ 2) * exp (-Real.pi * (x : ℂ) ^ 2) := by
  change polyGauss _ x = _
  simp [polyGauss]

/-- The archimedean factor `π^{-s/2} Γ(s/2 + 1)`. -/
noncomputable def arch (s : ℂ) : ℂ := (1 / (Real.pi : ℂ)) ^ (s / 2) * Gamma (s / 2 + 1)

lemma one_div_pi_ne : (1 / (Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]

lemma mellin_seed {s : ℂ} (hs : 0 < s.re) : mellin seed s = (s - 1) * arch s := by
  set g : ℝ → ℂ := fun u => (4 * Real.pi ^ 2 * (u : ℂ) ^ 2 - 6 * Real.pi * u) * exp (-(Real.pi * u))
  have e1 : mellin seed s = mellin (fun t : ℝ => g (t ^ (2 : ℝ))) s := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [g, seed_apply, Real.rpow_two]
    push_cast
    ring_nf
  have hw : 0 < (s / 2).re := by
    rw [show s / 2 = ((1 / 2 : ℝ) : ℂ) * s by push_cast; ring, re_ofReal_mul]; linarith
  have key : ∀ k : ℂ, 0 < k.re → IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (k - 1) * exp (-(Real.pi * t))) (Ioi 0) := fun k hk => by
    by_contra h
    have h1 := Complex.integral_cpow_mul_exp_neg_mul_Ioi hk Real.pi_pos
    rw [integral_undef h] at h1
    exact mul_ne_zero
      ((cpow_ne_zero_iff_of_exponent_ne_zero
      (by rintro rfl; simp at hk)).2 one_div_pi_ne) (Gamma_ne_zero_of_re_pos hk) h1.symm
  have h2 : 0 < (s / 2 + 2).re := by rw [add_re]; norm_num; linarith
  have h3 : 0 < (s / 2 + 1).re := by rw [add_re]; norm_num; linarith
  have e2 : mellin g (s / 2) = 4 * Real.pi ^ 2 * ((1 / Real.pi) ^ (s / 2 + 2) * Gamma (s / 2 + 2)) -
      6 * Real.pi * ((1 / Real.pi) ^ (s / 2 + 1) * Gamma (s / 2 + 1)) := by
    rw [← Complex.integral_cpow_mul_exp_neg_mul_Ioi h2 Real.pi_pos,
      ← Complex.integral_cpow_mul_exp_neg_mul_Ioi h3 Real.pi_pos, ← integral_const_mul,
      ← integral_const_mul, ← integral_sub ((key _ h2).const_mul _) ((key _ h3).const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 (ne_of_gt ht)
    simp only [g, smul_eq_mul]
    rw [show s / 2 + 2 - 1 = (s / 2 - 1) + (2 : ℕ) by push_cast; ring,
      show s / 2 + 1 - 1 = (s / 2 - 1) + (1 : ℕ) by push_cast; ring, cpow_add _ _ ht0,
      cpow_add _ _ ht0, cpow_natCast, cpow_natCast]
    ring
  have e3 : Gamma (s / 2 + 2) = (s / 2 + 1) * Gamma (s / 2 + 1) := by
    rw [show s / 2 + 2 = (s / 2 + 1) + 1 by ring, Gamma_add_one]
    intro h
    rw [h] at h3
    simp at h3
  have hpi : (Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [e1, mellin_comp_rpow, ofReal_ofNat, e2, e3, arch,
    show s / 2 + 2 = s / 2 + (2 : ℕ) by push_cast; ring, cpow_add _ _ one_div_pi_ne,
    cpow_add _ _ one_div_pi_ne, cpow_natCast, cpow_one, real_smul]
  push_cast
  rw [abs_of_pos two_pos]
  push_cast
  field_simp
  ring

lemma thetaClass_seed : ThetaClass seed where
  even x := by
    simp only [seed_apply, ofReal_neg, neg_sq, show (-(x : ℂ)) ^ 4 = (x : ℂ) ^ 4 by ring]
  zero := by simp [seed_apply]
  integral := by
    have h1 : mellin seed 1 = ∫ x in Ioi (0 : ℝ), seed x := by simp [mellin]
    have h2 : ∫ x in Iic (0 : ℝ), seed x = ∫ x in Ioi (0 : ℝ), seed x := by
      have := integral_comp_neg_Iic (0 : ℝ) fun x => seed x
      rw [neg_zero] at this
      rw [← this]
      simp only [seed_apply, ofReal_neg, neg_sq, (by intro x; ring : ∀ x : ℂ, (-x) ^ 4 = x ^ 4)]
    rw [← intervalIntegral.integral_Iic_add_Ioi seed.integrable.integrableOn
      seed.integrable.integrableOn, h2, ← h1, mellin_seed (by simp)]
    simp

lemma arch_ne_zero {s : ℂ} (hs : 0 < s.re) : arch s ≠ 0 := by
  refine mul_ne_zero (by simp [cpow_eq_zero_iff, Real.pi_ne_zero]) (Gamma_ne_zero_of_re_pos ?_)
  rw [show s / 2 = ((1 / 2 : ℝ) : ℂ) * s by push_cast; ring, add_re, re_ofReal_mul, one_re]
  linarith

lemma arch_eq {s : ℂ} (hs : s ≠ 0) : arch s = s / 2 * Gammaℝ s := by
  rw [arch, Gamma_add_one _ (div_ne_zero hs two_ne_zero), Gammaℝ_def, one_div, inv_cpow,
    ← cpow_neg, neg_div]
  · ring
  · rw [arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_pos.ne

/-- The transform of the theta function of the seed. -/
noncomputable abbrev xi : ℂ → ℂ := jet (theta seed) 0

lemma xi_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) : xi (s - 1 / 2) = zetaNum s * arch s := by
  have h := sub_one_mul_jet thetaClass_seed hs
  rw [mellin_seed hs, mul_left_comm] at h
  exact mul_left_cancel₀ (sub_ne_zero.2 hs1) h

lemma xi_eq_completed {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    xi (s - 1 / 2) = s * (s - 1) / 2 * completedRiemannZeta s := by
  have h0 : s ≠ 0 := by rintro rfl; simp at hs
  rw [xi_eq hs hs1, zetaNum_of_ne hs1, arch_eq h0, riemannZeta_def_of_ne_zero h0]
  field_simp [Gammaℝ_ne_zero_of_re_pos hs]

/-- The transform of the theta function of the seed is half of `WeilExplicit.xi`, shifted. -/
theorem xi_eq_half_WeilExplicit (s : ℂ) : xi (s - 1 / 2) = 1 / 2 * WeilExplicit.xi s := by
  have hd := thetaClass_seed.rapid.differentiable_jet
  have h := AnalyticOnNhd.eq_of_eventuallyEq (f := fun s => xi (s - 1 / 2))
    (g := fun s => 1 / 2 * WeilExplicit.xi s) (z₀ := 2)
    (fun w _ => (hd.comp (differentiable_id.sub_const _)).analyticAt w)
    (fun w _ => (WeilExplicit.differentiable_xi.const_mul _).analyticAt w) ?_
  · exact congrFun h s
  · filter_upwards [(isOpen_lt (f := fun _ : ℂ ↦ (0 : ℝ)) continuous_const continuous_re).mem_nhds
      (show (0 : ℝ) < (2 : ℂ).re by norm_num), eventually_ne_nhds (show (2 : ℂ) ≠ 1 by norm_num)]
      with w hw h1
    have h0 : w ≠ 0 := by rintro rfl; simp at hw
    rw [xi_eq_completed hw h1, WeilExplicit.xi_eq_completed h0 h1]
    ring

lemma analyticOrderAt_xi_shift (s : ℂ) :
    analyticOrderAt xi (s - 1 / 2) = analyticOrderAt WeilExplicit.xi s := by
  rw [← analyticOrderAt_comp_of_deriv_ne_zero (f := xi) (g := fun w : ℂ => w - 1 / 2) (z₀ := s)
      (by fun_prop) (by simp),
    analyticOrderAt_congr (g := (fun _ => (1 / 2 : ℂ)) * WeilExplicit.xi)
      (Eventually.of_forall xi_eq_half_WeilExplicit),
    analyticOrderAt_mul analyticAt_const (WeilExplicit.differentiable_xi.analyticAt s),
    analyticAt_const.analyticOrderAt_eq_zero.2 (by norm_num), zero_add]

lemma xi_neg (z : ℂ) : xi (-z) = xi z := by
  rw [show -z = 1 - (z + 1 / 2) - 1 / 2 by ring, xi_eq_half_WeilExplicit,
    WeilExplicit.xi_one_sub, ← xi_eq_half_WeilExplicit, add_sub_cancel_right]

/-- The transform of the theta function of the seed is the Riemann `ξ` function. -/
theorem xi_eq_riemann {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xi (s - 1 / 2) = s * (s - 1) / 2 * completedRiemannZeta s := by
  rw [xi_eq_half_WeilExplicit, WeilExplicit.xi_eq_completed hs0 hs1]
  ring

/-- In the half-plane `Re s > 0`, the order of `ξ` is the multiplicity of the zeta zero. -/
lemma analyticOrderAt_xi {s : ℂ} (hs : 0 < s.re) : analyticOrderAt xi (s - 1 / 2) = zeroMult s := by
  rw [analyticOrderAt_xi_shift]
  by_cases h : s ∈ stripZeros
  · rw [WeilExplicit.xi_order_eq h]
    exact (Nat.cast_analyticOrderNatAt
      (WeilExplicit.zeta_order_ne_top (by rintro rfl; exact absurd h.2.2 (by simp)))).symm
  · have hz : riemannZeta s ≠ 0 := fun hz =>
      h ⟨hz, hs, not_le.1 fun h1 => riemannZeta_ne_zero_of_one_le_re h1 hz⟩
    rw [analyticOrderAt_eq_zero.2 (.inr (mt WeilExplicit.xi_eq_zero_iff.1 h))]
    simp [WeilExplicit.zeroMult, analyticOrderNatAt, analyticOrderAt_eq_zero.2 (.inr hz)]

/-- The order of `ξ` at `z` is the multiplicity of the zero `1/2 + z`, if it lies in the strip. -/
lemma lt_analyticOrderAt_xi {z : ℂ} {m : ℕ} (hm : m < analyticOrderAt xi z) :
    m < zeroMult (1 / 2 + z) ∧ 1 / 2 + z ∈ stripZeros := by
  rw [← add_sub_cancel_left (1 / 2 : ℂ) z] at hm
  have hs := WeilExplicit.xi_eq_zero_iff.1 (apply_eq_zero_of_analyticOrderAt_ne_zero
    (pos_of_gt (analyticOrderAt_xi_shift _ ▸ hm)).ne')
  rw [analyticOrderAt_xi hs.2.1] at hm
  exact ⟨by exact_mod_cast hm, hs⟩

lemma theta_translate (t : ℝ) : ∃ f, ThetaClass f ∧ ∀ x, theta f x = theta seed (x - t) := by
  have hi := thetaClass_seed.integral
  refine ⟨(Real.exp (-t / 2) : ℂ) • dilate (Real.exp (-t)) (Real.exp_pos _) seed, ?_, fun x => ?_⟩
  · refine ⟨fun x => ?_, ?_, ?_⟩
    · simp [dilate_apply, thetaClass_seed.even]
    · simp [dilate_apply, thetaClass_seed.zero]
    · simp only [smul_apply, dilate_apply, smul_eq_mul]
      rw [integral_const_mul, Measure.integral_comp_mul_left, hi]
      simp
  · simp only [theta, smul_apply, dilate_apply, smul_eq_mul, tsum_mul_left]
    rw [← mul_assoc, ← ofReal_mul, ← Real.exp_add]
    have e1 : x / 2 + -t / 2 = (x - t) / 2 := by ring
    have e2 : ∀ n : ℕ, Real.exp (-t) * ((n + 1) * Real.exp x) = (n + 1) * Real.exp (x - t) :=
      fun n => by rw [sub_eq_add_neg x t, Real.exp_add]; ring
    simp only [e1, e2]

end Masullo.Synthesis
