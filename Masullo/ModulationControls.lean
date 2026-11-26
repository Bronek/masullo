import Masullo.Modulation

/-!
# Controls for the sharpness of the averaged trace

`Masullo.Trace.trace_eq_of_integral_small` needs integrals below `ε` at arbitrarily large `T`.
Without that quantifier the hypothesis is vacuous.
-/

open Set MeasureTheory

namespace Masullo.Trace.Controls

/-- Without "arbitrarily large `T`", the hypothesis of `trace_eq_of_integral_small` always holds:
for every `ε > 0` some `T > 0` has `∫ τ in -T..T, ‖Weil's functional at φ.modulate τ - s τ‖ ≤ ε`,
by continuity of the integrand. -/
theorem integral_small_of_small_T {a : ℝ} (ha : 0 < a) (φ : TestFunction) (s : ℝ → ℂ)
    (hs : ∀ τ, HasTrace (induced ha (φ.modulate τ)) (s τ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∫ τ in -T..T, ‖(φ.modulate τ).efFunctional - s τ‖ ≤ ε := by
  have hg := continuous_modulate_sub ha φ s hs
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hg.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨by norm_num, by norm_num⟩)
  refine ⟨min 1 (ε / (2 * C + 2)), lt_min one_pos (by positivity), ?_⟩
  set T := min 1 (ε / (2 * C + 2))
  have hT1 : T ≤ 1 := min_le_left _ _
  have hT2 : T ≤ ε / (2 * C + 2) := min_le_right _ _
  have hT0 : 0 < T := lt_min one_pos (by positivity)
  have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -T ≤ T)
    (hg.intervalIntegrable _ _) (intervalIntegrable_const (c := C)) fun τ hτ => by
      have := hC τ ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      rwa [norm_norm] at this
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  rw [le_div_iff₀ (by positivity)] at hT2
  nlinarith

end Masullo.Trace.Controls
