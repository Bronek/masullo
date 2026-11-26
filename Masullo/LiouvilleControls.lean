import Masullo.Liouville

/-!
# Controls for the Liouville criteria

`WindowBound` and `MeanBound` at `θ = 1`, where the criteria say nothing; and a counterexample to
`Landau.ContinuesMero.eq_empty_of_window` without the condition `g ρ ≠ 0` of `ContinuesMero.pole`.
-/

open MeasureTheory Complex Set Filter Topology Metric

namespace Masullo.Liouville.Controls

/-- `WindowBound` holds at `θ = 1` with `C = 1`, since `|liouvilleSum x| ≤ x`; either sign
serves. -/
theorem window_at_exponent_one (δ : ℝ) : WindowBound 1 δ 1 := by
  intro X
  refine ⟨max X 2, le_max_left _ _, 1, .inl rfl, fun x hx => ?_⟩
  have := abs_le.1 (abs_liouvilleSum_le (by linarith [hx.1, le_max_right X 2] : (0 : ℝ) ≤ x))
  rw [Real.rpow_one]
  linarith

/-- `MeanBound` holds at `θ = 1` with `h = 1` and `C = 2`, since
`|liouvilleSum (t + 1) - liouvilleSum t| ≤ 2`; either sign serves. -/
theorem mean_at_exponent_one (δ : ℝ) : MeanBound 1 δ 2 := by
  intro X
  set Y := max X 2
  have hY : 2 ≤ Y := le_max_right _ _
  refine ⟨Y, le_max_left _ _, 1, one_pos, by rw [Real.rpow_one]; linarith, 1, .inl rfl,
    fun x hx => ?_⟩
  have hg := intervalIntegrable_increment 1 1 Y x
  rw [Real.rpow_one]
  calc (∫ t in Y..x, max (1 * (liouvilleSum (t + 1) - liouvilleSum t) / 1) 0)
      ≤ ∫ _ in Y..x, (2 : ℝ) := by
        refine intervalIntegral.integral_mono_on hx.1 ⟨hg.1.pos_part, hg.2.pos_part⟩
          intervalIntegrable_const fun t ht => max_le ?_ (by norm_num)
        have := abs_le.1 (abs_liouvilleSum_sub_le (by linarith [ht.1] : (0 : ℝ) ≤ t)
          (le_add_of_nonneg_right zero_le_one))
        rw [one_mul, div_one]
        linarith
    _ ≤ 2 * x := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        linarith

/-- The condition `g ρ ≠ 0` of `ContinuesMero.pole` is needed. The zero function, with transform
`0` and a claimed pole at `1 + i` of numerator `0`, meets every other condition of
`ContinuesMero f H Z A c 0` and every hypothesis of `ContinuesMero.eq_empty_of_window`, yet
`Z ≠ ∅`. The pole is not real, so the sign condition at real poles holds vacuously; a real
claimed pole would violate it, since a numerator vanishing near the pole has real part `0`. -/
theorem pole_ne_zero_needed : ∃ (f : ℝ → ℝ) (H : ℂ → ℂ) (Z : Set ℂ) (A c : ℝ),
    Measurable f ∧ (∀ u, 0 ≤ u → |f u| ≤ A * Real.exp (c * u)) ∧
    (∀ s : ℂ, c < s.re → H s = ∫ u in Ioi (0 : ℝ), (f u : ℂ) * cexp (-(s * u))) ∧
    (∀ s : ℂ, 0 < s.re → s ∉ Z → AnalyticAt ℂ H s) ∧
    (∀ (s : ℂ) (r : ℝ), (Z ∩ closedBall s r).Finite) ∧ (∀ ρ ∈ Z, ρ.re ∈ Ioc 0 c) ∧
    (∀ ρ ∈ Z, ∃ (m : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, H s = g s / (s - ρ) ^ (m + 1)) ∧
    (∀ ρ ∈ Z, ρ.im = 0 → ∃ (m : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g ρ ∧ (g ρ).re < 0 ∧
      ∀ᶠ s in 𝓝[≠] ρ, H s = g s / (s - ρ) ^ (m + 1)) ∧
    (∀ X, ∃ U ≥ X, ∀ u ∈ Icc U ((1 + 1) * U), 0 ≤ f u) ∧ Z ≠ ∅ :=
  ⟨fun _ => 0, fun _ => 0, {1 + I}, 0, 1, measurable_const, by simp, by simp,
    fun _ _ _ => analyticAt_const, fun _ _ => (finite_singleton _).subset inter_subset_left,
    fun ρ hρ => by simp [mem_singleton_iff.1 hρ],
    fun _ _ => ⟨0, fun _ => 0, analyticAt_const, .of_forall fun _ => by simp⟩,
    fun ρ hρ hi => by simp [mem_singleton_iff.1 hρ] at hi,
    fun X => ⟨X, le_rfl, fun _ _ => le_rfl⟩, singleton_ne_empty _⟩

end Masullo.Liouville.Controls
