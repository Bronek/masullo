import Masullo.Runs
import Masullo.DyadicControls

/-!
# Controls for fixed-ratio sign runs

At ratio `R = 1` the run hypothesis of `exists_rightmost_of_runs` holds trivially, so it carries
information only through `1 < R`. The one-sided bound of `trace_width_of_bound` holds at
`θ = 1` for every ratio, by Chebyshev's bound, so it carries information only through `θ < 1`.
The two-point factor attached to a zero of ordinate `γ`
also cancels a zero of the same real part and ordinate `3γ`, so an arbitrary choice of
survivor can fail; choosing one of least positive ordinate prevents this cancellation.
-/

open Complex Set
open scoped Real

namespace Masullo.Runs.Controls

open Window

/-- Every window of ratio one is a single point, where `dyadicDiff` has a sign. -/
theorem runs_at_ratio_one : ∀ Y₀, ∃ Y ≥ Y₀, (∀ x ∈ Icc Y (1 * Y), 0 ≤ dyadicDiff x) ∨
    (∀ x ∈ Icc Y (1 * Y), dyadicDiff x ≤ 0) := by
  intro Y₀
  refine ⟨Y₀, le_rfl, ?_⟩
  rw [one_mul, Icc_self]
  rcases le_total 0 (dyadicDiff Y₀) with h | h
  · exact .inl fun x hx => (mem_singleton_iff.1 hx) ▸ h
  · exact .inr fun x hx => (mem_singleton_iff.1 hx) ▸ h

/-- The upper bound with `θ = 1` holds on every window. -/
theorem bound_at_exponent_one (R : ℝ) : ∀ Y₀, ∃ Y ≥ Y₀,
    (∀ x ∈ Icc Y (R * Y), -((2 * (Real.log 4 + 4)) * x ^ (1 : ℝ)) ≤ dyadicDiff x) ∨
    (∀ x ∈ Icc Y (R * Y), dyadicDiff x ≤ (2 * (Real.log 4 + 4)) * x ^ (1 : ℝ)) := fun Y₀ =>
  ⟨max Y₀ 1, le_max_left _ _, .inr fun x hx => by
    have h1 := (le_max_right Y₀ 1).trans hx.1
    have h2 := Window.Controls.dyadicSum_le (X := 2 * x) (by linarith)
    rw [Real.rpow_one, dyadicDiff]
    linarith [Window.Controls.dyadicSum_nonneg x]⟩

/-- The factor attached to `β + iγ` cancels `β + 3iγ`. -/
theorem factor_odd_multiple {β γ : ℝ} (hγ : 0 < γ) :
    factor (mass ⟨β, γ⟩) (shift ⟨β, γ⟩) ⟨β, 3 * γ⟩ = 0 := by
  rw [factor_eq_zero_iff, cexp_mul_real]
  have e : (3 * γ) * shift ⟨β, γ⟩ = π + 2 * π := by
    simp only [shift]; field_simp; ring
  rw [e, ofReal_add, add_mul, Complex.exp_add, exp_pi_mul_I,
    show ((2 * π : ℝ) : ℂ) * I = (1 : ℤ) * (2 * π * I) by push_cast; ring,
    exp_int_mul_two_pi_mul_I]
  ring

end Masullo.Runs.Controls
