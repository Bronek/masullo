module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

/-! # Bessel and gamma factors for the Mellin transform of Patterson's series -/

@[expose] public noncomputable section

open MeasureTheory Filter Asymptotics
open scoped Topology ComplexConjugate

namespace Masullo.QRH.MeanSquare

/-- The modified Bessel function on the positive real axis, defined by the integral in
DLMF 10.32.9. Only positive arguments occur in the theta expansion.
<https://dlmf.nist.gov/10.32.E9> -/
def besselK (ν : ℂ) (x : ℝ) : ℂ :=
  ∫ t : ℝ in Set.Ioi 0, (Real.exp (-x * Real.cosh t) : ℂ) * Complex.cosh (ν * t)

/-- Real order gives real values along the positive axis. -/
lemma besselK_conj_real (ν x : ℝ) : conj (besselK (ν : ℂ) x) = besselK (ν : ℂ) x := by
  rw [besselK, ← integral_conj]
  simp only [map_mul, Complex.conj_ofReal, ← Complex.cosh_conj]

/-- F. W. J. Olver and L. C. Maximon, *NIST Handbook of Mathematical Functions* (2010),
10.43.19, p. 259. The Mellin transform includes convergence on the printed domain.
<https://dlmf.nist.gov/10.43.E19> -/
def DLMFBesselMellin : Prop :=
  ∀ ν μ : ℂ, |ν.re| < μ.re →
    HasMellin (besselK ν) μ
      ((2 : ℂ) ^ (μ - 2) * Complex.Gamma ((μ - ν) / 2) * Complex.Gamma ((μ + ν) / 2))

/-- At order one third, horizontal differentiation gives the height exponent `2s`
in the Mellin integral, hence Mellin parameter `2s+1`. -/
theorem besselMellin_oneThird (h : DLMFBesselMellin) {s : ℂ} (hs : -(1 / 3 : ℝ) < s.re) :
    HasMellin (besselK (1 / 3)) (2 * s + 1)
      ((2 : ℂ) ^ (2 * s - 1) * Complex.Gamma (s + 1 / 3) * Complex.Gamma (s + 2 / 3)) := by
  have hs' : |(1 / 3 : ℂ).re| < (2 * s + 1).re := by
    norm_num [Complex.add_re, Complex.mul_re]
    linarith
  have hm := h (1 / 3) (2 * s + 1) hs'
  rw [show 2 * s + 1 - 2 = 2 * s - 1 by ring,
    show (2 * s + 1 - 1 / 3) / 2 = s + 1 / 3 by ring,
    show (2 * s + 1 + 1 / 3) / 2 = s + 2 / 3 by ring] at hm
  exact hm

/-- Rescale the Mellin integral by a positive frequency, as in the nonconstant
Fourier terms at height `v` with `a = 4π|μ|`. -/
theorem besselMellin_oneThird_scaled (h : DLMFBesselMellin) {s : ℂ} (hs : -(1 / 3 : ℝ) < s.re)
    {a : ℝ} (ha : 0 < a) :
    HasMellin (fun v => besselK (1 / 3) (a * v)) (2 * s + 1)
      ((a : ℂ) ^ (-(2 * s + 1)) *
        ((2 : ℂ) ^ (2 * s - 1) * Complex.Gamma (s + 1 / 3) * Complex.Gamma (s + 2 / 3))) := by
  obtain ⟨hc, hm⟩ := besselMellin_oneThird h hs
  exact ⟨(MellinConvergent.comp_mul_left ha).2 hc, by rw [mellin_comp_mul_left _ _ ha, hm]; rfl⟩

/-- Leading positive factor in the large-argument expansion of `K`. -/
def besselLeading (x : ℝ) : ℝ := Real.sqrt (Real.pi / (2 * x)) * Real.exp (-x)

/-- After `N` terms, the remainder of the normalized expansion is `O(x⁻ᴺ)`. -/
def HasHankelExpansion (f : ℝ → ℂ) (a : ℕ → ℂ) : Prop :=
  ∀ N : ℕ, (fun x : ℝ => f x / besselLeading x - ∑ k ∈ Finset.range N, a k / (x : ℂ) ^ k)
    =O[atTop] (fun x : ℝ => (x ^ N)⁻¹)

/-- R. A. Askey and R. Roy, *NIST Handbook* (2010), 5.11.9, p. 141. Both vertical
directions use the same threshold uniformly over bounded real parts.
<https://dlmf.nist.gov/5.11.E9> -/
def DLMFGammaVertical : Prop :=
  ∀ B ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ x y : ℝ, |x| ≤ B → T ≤ |y| →
    |‖Complex.Gamma (x + y * Complex.I)‖ /
      (Real.sqrt (2 * Real.pi) * |y| ^ (x - 1 / 2) * Real.exp (-Real.pi * |y| / 2)) - 1| < ε

end Masullo.QRH.MeanSquare
