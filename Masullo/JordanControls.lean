import Masullo.Jordan

/-!
# Controls for the Jordan sign criterion

At `τ = 0`, `jordan 0` is the unit of Dirichlet convolution, its partial sums are `1` from `x = 1`
on, and the sign hypothesis of `riemannZeta_ne_zero_of_jordanSign` holds with `ε = -1`; the
conclusion is then only the classical half-plane `Re s > 1`.
-/

open Set ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Masullo.Jordan.Controls

lemma jordan_zero : jordan 0 = 1 := by
  have : powNeg 0 = (ζ : ArithmeticFunction ℝ) := by
    ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    simp [powNeg_apply hn, natCoe_apply, zeta_apply, hn]
  rw [jordan, this, coe_moebius_mul_coe_zeta]

/-- The sign hypothesis of `riemannZeta_ne_zero_of_jordanSign` holds at `τ = 0` with `ε = -1`. -/
theorem jordanSign_at_zero (δ : ℝ) : ∀ X, ∃ Y ≥ X, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
    ∀ x ∈ Icc Y (Y ^ (1 + δ)), ε * DirichletWindow.partialSum (jordan 0) x ≤ 0 := fun X =>
  ⟨max X 1, le_max_left _ _, -1, .inr rfl, fun x hx => by
    have h1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using (le_max_right X 1).trans hx.1)
    simp [DirichletWindow.partialSum, jordan_zero, one_apply, h1]⟩

end Masullo.Jordan.Controls
