import Masullo.Runs
import Masullo.DyadicControls

/-!
# Controls for fixed-ratio sign runs

At ratio `R = 1` the hypothesis of `exists_rightmost_of_bound` holds trivially for every `C ≥ 0`
and `θ`, so it carries information only through `1 < R`. The one-sided bound of
`trace_width_of_bound` holds at `θ = 1` for every ratio, by Chebyshev's bound, so it carries
information only through `θ < 1`. The hypothesis of `ne_zero_of_dyadic_window` also holds at
`θ = 1`, where its conclusion is unconditional.
The two-point factor attached to a zero of ordinate `γ`
also cancels a zero of the same real part and ordinate `3γ`, so an arbitrary choice of
survivor can fail; choosing one of least positive ordinate prevents this cancellation.
-/

open Complex Set
open scoped Real

namespace Masullo.Runs.Controls

open Window
open Window.Controls (abs_dyadicDiff_le)

/-- Every window of ratio one is a single point, where `dyadicDiff` has a sign. -/
theorem bound_at_ratio_one {θ C : ℝ} (hC : 0 ≤ C) : ∀ Y₀, ∃ Y ≥ Y₀,
    (∀ x ∈ Icc Y (1 * Y), -(C * x ^ θ) ≤ dyadicDiff x) ∨
    (∀ x ∈ Icc Y (1 * Y), dyadicDiff x ≤ C * x ^ θ) := by
  intro Y₀
  have hC0 := mul_nonneg hC (Real.rpow_nonneg (le_max_right Y₀ 0) θ)
  refine ⟨max Y₀ 0, le_max_left _ _, ?_⟩
  rw [one_mul, Icc_self]
  rcases le_total 0 (dyadicDiff (max Y₀ 0)) with h | h
  · exact .inl fun x hx => by obtain rfl := mem_singleton_iff.1 hx; linarith
  · exact .inr fun x hx => by obtain rfl := mem_singleton_iff.1 hx; linarith

/-- The upper bound with `θ = 1` holds on every window. -/
theorem bound_at_exponent_one (R : ℝ) : ∀ Y₀, ∃ Y ≥ Y₀,
    (∀ x ∈ Icc Y (R * Y), -((2 * (Real.log 4 + 4)) * x ^ (1 : ℝ)) ≤ dyadicDiff x) ∨
    (∀ x ∈ Icc Y (R * Y), dyadicDiff x ≤ (2 * (Real.log 4 + 4)) * x ^ (1 : ℝ)) := fun Y₀ =>
  ⟨max Y₀ 1, le_max_left _ _, .inr fun x hx => by
    simpa using le_of_abs_le (abs_dyadicDiff_le (by linarith [(le_max_right Y₀ 1).trans hx.1]))⟩

/-- The lower bound with `θ = 1` holds on every window, with the sign `ε = 1`. -/
theorem dyadic_window_at_exponent_one (δ : ℝ) : ∀ X, ∃ Y ≥ X, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
    ∀ x ∈ Icc Y (Y ^ (1 + δ)), -((2 * (Real.log 4 + 4)) * x ^ (1 : ℝ)) ≤ ε * dyadicDiff x :=
  fun X => ⟨max X 1, le_max_left _ _, 1, .inl rfl, fun x hx => by
    simpa using neg_le_of_abs_le (abs_dyadicDiff_le (by linarith [(le_max_right X 1).trans hx.1]))⟩

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
