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
  have hP := intervalIntegral.continuous_primitive (μ := volume) (hg.intervalIntegrable ·  ·) 0
  have hF : Continuous fun T : ℝ => ∫ τ in -T..T, ‖(φ.modulate τ).efFunctional - s τ‖ :=
    (hP.sub (hP.comp continuous_neg)).congr fun T =>
      intervalIntegral.integral_interval_sub_left (hg.intervalIntegrable _ _)
        (hg.intervalIntegrable _ _)
  obtain ⟨T, h1, h2⟩ := ((((hF.tendsto 0).eventually (gt_mem_nhds (by simpa using hε))).filter_mono
    nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi 0))).exists
  exact ⟨T, h2, h1.le⟩

end Masullo.Trace.Controls
