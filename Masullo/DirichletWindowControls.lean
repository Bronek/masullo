import Masullo.DirichletWindow

/-!
# Controls for the Dirichlet window criterion

The Mertens window hypothesis at `θ = 1`, where the criterion says nothing, its fixed-sign
form, a one-sided bound with no sign to choose, and the restriction of a window bound to the perfect
powers, which shows the sampled hypothesis is no stronger than the pointwise one.
-/

open Set
open scoped ArithmeticFunction.Moebius

namespace Masullo.DirichletWindow.Controls

/-- The Mertens window hypothesis holds at `θ = 1` with `C = 1`, since `|partialSum μ x| ≤ x`;
either sign serves. -/
theorem mertensWindow_at_exponent_one (δ : ℝ) :
    WindowBound (partialSum fun n => (μ n : ℝ)) 1 δ 1 := fun X =>
  ⟨max X 0, le_max_left _ _, 1, .inl rfl, fun x hx => by
    rw [one_mul, Real.rpow_one, one_mul]
    exact (le_abs_self _).trans (abs_partialSum_le abs_moebius_le ((le_max_right X 0).trans hx.1))⟩

/-- An upper bound `∑_{n ≤ x} μ(n) ≤ C x ^ θ` on windows `[Y, Y ^ (1 + δ)]` for arbitrarily large
`Y`, with `θ ≥ 0`, rules out zeros of zeta to the right of `θ`. -/
theorem riemannZeta_ne_zero_of_mertens_le {θ δ C : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (h : ∀ X, ∃ Y ≥ X, ∀ x ∈ Icc Y (Y ^ (1 + δ)),
      partialSum (fun n => (μ n : ℝ)) x ≤ C * x ^ θ)
    {ρ : ℂ} (hρ : θ < ρ.re) : riemannZeta ρ ≠ 0 :=
  riemannZeta_ne_zero_of_mertensWindow hθ hδ (fun X =>
    let ⟨Y, hY, hb⟩ := h X; ⟨Y, hY, 1, .inl rfl, by simpa using hb⟩) hρ

/-- A window bound restricts to the perfect `m`-th powers with the same constant. -/
theorem powerWindowBound_of_windowBound {S : ℝ → ℝ} {m : ℕ} {θ δ C : ℝ}
    (h : WindowBound S θ δ C) : PowerWindowBound S m θ δ C := fun X =>
  let ⟨Y, hY, ε, hε, hw⟩ := h X; ⟨Y, hY, ε, hε, fun _ hj => hw _ hj⟩

end Masullo.DirichletWindow.Controls
