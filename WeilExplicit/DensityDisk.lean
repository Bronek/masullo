import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Area mean value inequality on a disc

A function holomorphic on a closed disc of radius `r` with `|f c| = 1` at the centre has
`∫_{|z - c| < r} |f|² ≥ π r²`. The proof applies the mean value property to `f²` on each circle
and integrates over the radius in polar coordinates.

Part of a Carlson-type mean-square zero-density argument due to OpenAI Codex (E36),
formalised by Claude.
-/

namespace WeilExplicit

open Complex MeasureTheory Set Metric Real

private theorem circle_lower {f : ℂ → ℂ} {c : ℂ} {r R : ℝ} (hR : 0 < R) (hRr : R ≤ r)
    (hf : DifferentiableOn ℂ f (closedBall c r)) (h1 : ‖f c‖ = 1) :
    ENNReal.ofReal (2 * π) ≤ ∫⁻ θ in Ioo (-π) π, ‖f (circleMap c R θ)‖ₑ ^ 2 := by
  have hsub : closure (ball c |R|) ⊆ closedBall c r := by
    rw [abs_of_pos hR]
    exact closure_ball_subset_closedBall.trans (closedBall_subset_closedBall hRr)
  have hg : DiffContOnCl ℂ (fun z ↦ f z ^ 2) (ball c |R|) :=
    ((hf.pow 2).mono hsub).diffContOnCl
  have hav := hg.circleAverage
  rw [Real.circleAverage_eq_integral_add (-π)] at hav
  have hshift := intervalIntegral.integral_comp_add_right
    (fun θ ↦ f (circleMap c R θ) ^ 2) (a := 0) (b := 2 * π) (-π)
  rw [hshift, show (0 : ℝ) + -π = -π by ring, show 2 * π + -π = π by ring] at hav
  have h2 : ∫ θ in (-π)..π, f (circleMap c R θ) ^ 2 = (2 * π : ℂ) * f c ^ 2 := by
    rw [← hav, Complex.real_smul]
    push_cast
    field_simp
  rw [intervalIntegral.integral_of_le (by linarith [pi_pos]), integral_Ioc_eq_integral_Ioo] at h2
  calc ENNReal.ofReal (2 * π) = ‖∫ θ in Ioo (-π) π, f (circleMap c R θ) ^ 2‖ₑ := by
        rw [h2, ← ofReal_norm, norm_mul, norm_pow, h1]
        simp [abs_of_pos Real.pi_pos]
    _ ≤ ∫⁻ θ in Ioo (-π) π, ‖f (circleMap c R θ) ^ 2‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = _ := by simp [enorm_pow]

/-- The area mean value inequality for `|f|²` on a disc where `|f|` is one at the centre. -/
theorem disk_lower {f : ℂ → ℂ} (hfm : Measurable f) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (closedBall c r)) (h1 : ‖f c‖ = 1) :
    ENNReal.ofReal (π * r ^ 2) ≤ ∫⁻ z in ball c r, ‖f z‖ₑ ^ 2 := by
  set h : ℂ → ENNReal := fun z ↦ ‖f z‖ₑ ^ 2
  have hm : Measurable h := hfm.enorm.pow_const 2
  set k : ℂ → ENNReal := fun z ↦ (ball c r).indicator h (c + z)
  have hk : Measurable k :=
    (hm.indicator measurableSet_ball).comp (measurable_const_add c)
  have hpm : Measurable fun p : ℝ × ℝ ↦ Complex.polarCoord.symm p := by
    simp_rw [Complex.polarCoord_symm_apply]; fun_prop
  have hFm : Measurable fun p : ℝ × ℝ ↦ ENNReal.ofReal p.1 • k (Complex.polarCoord.symm p) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).smul (hk.comp hpm)
  have hinner : ∀ R ∈ Ioo 0 r, ENNReal.ofReal (2 * π * R) ≤
      ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal R • k (Complex.polarCoord.symm (R, θ)) := by
    intro R hR
    have heq : ∀ θ, k (Complex.polarCoord.symm (R, θ)) = h (circleMap c R θ) := by
      intro θ
      have hc : c + Complex.polarCoord.symm (R, θ) = circleMap c R θ := by
        rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I, ← ofReal_cos,
          ← ofReal_sin]
      simp only [k]
      rw [hc, indicator_of_mem]
      rw [mem_ball, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hR.1]
      exact hR.2
    simp_rw [heq, smul_eq_mul]
    rw [lintegral_const_mul _ (by exact hm.comp (continuous_circleMap c R).measurable :
        Measurable fun θ ↦ h (circleMap c R θ)),
      ENNReal.ofReal_mul (by positivity), mul_comm]
    gcongr
    exact circle_lower hR.1 hR.2.le hf h1
  calc ENNReal.ofReal (π * r ^ 2) = ∫⁻ R in Ioo 0 r, ENNReal.ofReal (2 * π * R) := by
        rw [← ofReal_integral_eq_lintegral_ofReal
          ((by fun_prop : Continuous fun R : ℝ ↦ 2 * π * R).integrableOn_Icc.mono_set
            Ioo_subset_Icc_self)
          (ae_restrict_of_forall_mem measurableSet_Ioo fun R hR ↦ by
            simp only [Pi.zero_apply]; have := hR.1; positivity),
          ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le,
          intervalIntegral.integral_const_mul, integral_id]
        congr 1; ring
    _ ≤ ∫⁻ R in Ioo 0 r, ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal R • k (Complex.polarCoord.symm (R, θ)) :=
        setLIntegral_mono' measurableSet_Ioo hinner
    _ = ∫⁻ p in Ioo 0 r ×ˢ Ioo (-π) π, ENNReal.ofReal p.1 • k (Complex.polarCoord.symm p) := by
        rw [Measure.volume_eq_prod, setLIntegral_prod _ hFm.aemeasurable]
    _ ≤ ∫⁻ p in Complex.polarCoord.target, ENNReal.ofReal p.1 • k (Complex.polarCoord.symm p) :=
        lintegral_mono_set (prod_mono Ioo_subset_Ioi_self subset_rfl)
    _ = ∫⁻ z, k z := Complex.lintegral_comp_polarCoord_symm k
    _ = ∫⁻ z, (ball c r).indicator h z := lintegral_add_left_eq_self ((ball c r).indicator h) c
    _ = _ := lintegral_indicator measurableSet_ball h

end WeilExplicit
