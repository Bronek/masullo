import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.SumCoeff

/-! # The fractional-part integral for zeta -/

namespace WeilExplicit

open Complex MeasureTheory Set Filter Asymptotics
open scoped Topology

private noncomputable def remainder : ℝ → ℂ :=
  (Ioi 1).indicator fun x : ℝ ↦ ((Int.fract x : ℝ) : ℂ)

private theorem norm_remainder_le (x : ℝ) : ‖remainder x‖ ≤ 1 := by
  by_cases hx : x ∈ Ioi 1
  · simpa [remainder, hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
      using (Int.fract_lt_one x).le
  · simp [remainder, hx]

private theorem measurable_remainder : Measurable remainder :=
  (Complex.measurable_ofReal.comp measurable_fract).indicator measurableSet_Ioi

private theorem differentiableAt_remainder_mellin {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z ↦ mellin remainder (-z)) s := by
  refine (mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := (-s).re - 1)
    ((locallyIntegrableOn_const (1 : ℝ)).mono measurable_remainder.aestronglyMeasurable
      (.of_forall fun x ↦ by simpa using norm_remainder_le x))
        ?_ (by simpa) ?_ (by linarith)).comp s
      (differentiableAt_id.neg)
  · apply isBigO_of_le
    intro x
    simpa using norm_remainder_le x
  · refine isBigO_iff.mpr ⟨1, ?_⟩
    filter_upwards [mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx
    simp [remainder, not_lt.mpr hx.le]

private theorem mellin_remainder (s : ℂ) :
    mellin remainder (-s) =
      ∫ x : ℝ in Ioi 1, (x : ℂ) ^ (-s - 1) * ((Int.fract x : ℝ) : ℂ) := by
  simp only [mellin, remainder, smul_eq_mul,
    ← indicator_mul_right (Ioi 1) (fun x : ℝ ↦ (x : ℂ) ^ (-s - 1))]
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi (by norm_num))]

private theorem norm_remainder_integrand {s : ℂ} {x : ℝ} (hx : x ∈ Ioi 1) :
    ‖(x : ℂ) ^ (-s - 1) * ((Int.fract x : ℝ) : ℂ)‖ ≤ x ^ (-s.re - 1) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx), sub_re, neg_re, one_re]
  apply mul_le_of_le_one_right (Real.rpow_nonneg (zero_lt_one.trans hx).le _)
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
    using (Int.fract_lt_one x).le

private theorem integrableOn_remainder {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ (-s - 1) * ((Int.fract x : ℝ) : ℂ)) (Ioi 1) := by
  apply (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) zero_lt_one).mono'
  · exact (Measurable.mul (by fun_prop : Measurable fun x : ℝ ↦ (x : ℂ) ^ (-s - 1))
      (Complex.measurable_ofReal.comp measurable_fract)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    exact norm_remainder_integrand hx

private theorem zeta_eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * mellin remainder (-s) := by
  have hL := LSeries_eq_mul_integral' (1 : ℕ → ℂ) zero_le_one hs
    (by simpa using (isBigO_refl (fun n : ℕ ↦ (n : ℝ)) atTop))
  rw [LSeries_one_eq_riemannZeta hs] at hL
  rw [hL, mellin_remainder, div_eq_mul_inv, ← mul_sub]
  congr 1
  have hpow : (-s).re < -1 := by simpa
  rw [show (s - 1)⁻¹ = ∫ x : ℝ in Ioi 1, (x : ℂ) ^ (-s) by
    rw [integral_Ioi_cpow_of_lt hpow zero_lt_one]
    rw [ofReal_one, one_cpow, show -s + 1 = -(s - 1) by ring, neg_div_neg_eq, one_div]]
  rw [← integral_sub (integrableOn_Ioi_cpow_of_lt hpow zero_lt_one)
    (integrableOn_remainder (zero_lt_one.trans hs))]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  have hx' : 0 < x := zero_lt_one.trans hx
  have hfloor : (⌊x⌋₊ : ℂ) = (⌊x⌋ : ℤ) := by exact_mod_cast Int.natCast_floor_eq_floor hx'.le
  have hp : (x : ℂ) ^ (-s) = (x : ℂ) ^ (-s - 1) * x := by
    conv_lhs => rw [← sub_add_cancel (-s) 1, cpow_add _ _ (ofReal_ne_zero.mpr hx'.ne'), cpow_one]
  simp only [Pi.one_apply, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul, mul_one, hfloor, show -(s + 1) = -s - 1 by ring, Int.fract,
    Complex.ofReal_sub, Complex.ofReal_intCast, hp]
  ring

/-- Partial summation gives a fractional-part integral for zeta on Re s > 0 away from its pole. -/
theorem zeta_eq_fractional_part_integral {s : ℂ} (hs : 0 < s.re) (h₁ : s ≠ 1) :
    riemannZeta s = s / (s - 1) -
      s * ∫ x : ℝ in Ioi 1, (x : ℂ) ^ (-s - 1) * ((Int.fract x : ℝ) : ℂ) := by
  let F (z : ℂ) := z - (z - 1) * z * mellin remainder (-z)
  have hF : AnalyticOnNhd ℂ F {z | 0 < z.re} := by
    apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const continuous_re)
    intro z hz
    exact (differentiableAt_id.sub (((differentiableAt_id.sub_const 1).mul differentiableAt_id).mul
      (differentiableAt_remainder_mellin hz))).differentiableWithinAt
  have heq : EqOn riemannZeta₁ F {z | 0 < z.re} := by
    have hA : AnalyticOnNhd ℂ riemannZeta₁ {z | 0 < z.re} :=
      differentiable_riemannZeta₁.differentiableOn.analyticOnNhd
        (isOpen_lt continuous_const continuous_re)
    apply hA.eqOn_of_preconnected_of_eventuallyEq hF
      (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by norm_num)
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (2 : ℂ) ∈ {z | 1 < z.re})] with z hz
    have h₁z : z ≠ 1 := by intro h; simp [h] at hz
    have hzeta := zeta_eq_of_one_lt hz
    rw [riemannZeta_eq_inv_sub_mul h₁z] at hzeta
    dsimp [F]
    field_simp [sub_ne_zero.mpr h₁z] at hzeta
    linear_combination hzeta
  rw [riemannZeta_eq_inv_sub_mul h₁, heq hs, ← mellin_remainder]
  dsimp [F]
  field_simp [sub_ne_zero.mpr h₁]

/-- Growth in the right half-plane, with the contribution of the pole explicit. -/
theorem norm_zeta_le {s : ℂ} (hs : 0 < s.re) (h₁ : s ≠ 1) :
    ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by
  rw [zeta_eq_fractional_part_integral hs h₁]
  grw [norm_sub_le, norm_div, norm_mul]
  rw [div_eq_mul_inv ‖s‖ s.re]
  gcongr
  refine (norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt
    (by linarith : -s.re - 1 < -1) zero_lt_one) ?_).trans ?_
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    exact norm_remainder_integrand hx
  · rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
    simp

end WeilExplicit
