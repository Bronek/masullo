import Masullo.ChebyshevWindow

/-!
# Controls for the Chebyshev window criterion

The window hypothesis at `θ = 1`, where the criterion says nothing: `x - ψ x ≤ x` since `ψ ≥ 0`,
so the sign `ε = -1` serves with `C = 1`.
-/

open Set

namespace Masullo.ChebyshevWindow.Controls

/-- `WindowBound (fun x => ψ x - x) 1 δ 1` holds with `ε = -1`. -/
theorem psiWindow_at_exponent_one (δ : ℝ) :
    DirichletWindow.WindowBound (fun x => Chebyshev.psi x - x) 1 δ 1 := fun X =>
  ⟨max X 0, le_max_left _ _, -1, .inr rfl, fun x _ => by
    rw [one_mul, Real.rpow_one]
    linarith [Chebyshev.psi_nonneg x]⟩

end Masullo.ChebyshevWindow.Controls
