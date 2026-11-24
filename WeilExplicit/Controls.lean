import WeilExplicit.ExplicitFormula
import WeilExplicit.PrimeSupport
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! # Semantic controls for the test class and zero weights -/

namespace WeilExplicit

open WeilExplicit (transform)

open MeasureTheory Complex
open scoped FourierTransform ComplexConjugate

/-- A normalized smooth bump realizes transform value one at frequency zero. -/
theorem exists_transform_zero_eq_one :
    ∃ k : ℝ → ℂ, ContDiff ℝ 2 k ∧ HasCompactSupport k ∧ transform k 0 = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let k (x : ℝ) : ℂ := b.normed volume x
  refine ⟨k, ofRealCLM.contDiff.comp b.contDiff_normed, ?_, ?_⟩
  · exact b.hasCompactSupport_normed.comp_left (g := ((↑) : ℝ → ℂ)) (by simp)
  · simp [transform, k, integral_complex_ofReal, b.integral_normed]

/-- Every index of the zero sum has strictly positive weight. -/
theorem strip_weight_ne_zero (ρ : stripZeros) : (zeroMult ρ : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (zeroMult_pos ρ.property).ne'

/-- The Fourier convention fixes both the sign and the factor 2π in the angular frequency. -/
theorem fourier_convention (k : ℝ → ℂ) (w : ℝ) :
    𝓕 k w = ∫ u : ℝ, k u * exp (I * ((-2*Real.pi*w : ℝ) : ℂ) * u) :=
  fourier_eq_transform k w

/-- The finite-support and integrability guarantees apply to the expressions in Weil's formula. -/
theorem explicit_formula_with_guards (k : ℝ → ℂ) (hk : ContDiff ℝ 2 k) (hs : HasCompactSupport k) :
    let h (z : ℂ) := ∫ u : ℝ, k u * Complex.exp (Complex.I * z * u)
    let P (n : ℕ) := ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n))
    let A (r : ℝ) := h r *
      (((Complex.digamma (1/4 + Complex.I * r/2)).re - Real.log Real.pi : ℝ) : ℂ)
    HasSum (fun ρ : stripZeros => (zeroMult ρ : ℂ) * h (((ρ : ℂ) - 1/2) / Complex.I))
      (h (Complex.I/2) + h (-Complex.I/2) - (∑' n, P n) + (1/(2*(Real.pi:ℂ))) * ∫ r, A r)
      ∧ P.HasFiniteSupport ∧ Integrable A :=
  ⟨explicit_formula hk hs, prime_sum_finite_support hs, integrable_archimedean hk hs⟩

/-- The first two natural indices contribute zero to the prime sum. -/
theorem prime_coeff_zero_one :
    ArithmeticFunction.vonMangoldt 0 / Real.sqrt 0 = 0 ∧
    ArithmeticFunction.vonMangoldt 1 / Real.sqrt 1 = 0 := by simp

/-- Multiplicity vanishes wherever zeta is analytic and nonzero. -/
theorem zeroMult_eq_zero {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) : zeroMult s = 0 := by
  simp [zeroMult, analyticOrderNatAt, (analyticOn_riemannZeta s hs).analyticOrderAt_eq_zero.mpr hz]

/-- Conjugate strip zeros have equal multiplicity, detected by the first nonzero derivative. -/
theorem zeroMult_conj (ρ : stripZeros) : zeroMult (conj (ρ:ℂ)) = zeroMult ρ := by
  have hd (n : ℕ) : conj ∘ iteratedDeriv n riemannZeta ∘ conj = iteratedDeriv n riemannZeta := by
    induction n with
    | zero => ext z; simp [riemannZeta_conj]
    | succ n ih => simpa only [iteratedDeriv_succ, deriv_conj_conj] using congrArg deriv ih
  have he (n : ℕ) : iteratedDeriv n riemannZeta (conj (ρ:ℂ)) =
      conj (iteratedDeriv n riemannZeta ρ) := by
    simpa [Function.comp_def] using (congrFun (hd n) (conj (ρ:ℂ))).symm
  have h : (ρ:ℂ) ≠ 1 := fun e ↦ by simpa [e] using ρ.property.2.2
  have h' : conj (ρ:ℂ) ≠ 1 := fun e ↦ h (by simpa using congrArg conj e)
  suffices analyticOrderAt riemannZeta (conj (ρ:ℂ)) = (zeroMult ρ : ℕ∞) by
    simpa [zeroMult, analyticOrderNatAt] using congrArg ENat.toNat this
  rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (analyticOn_riemannZeta _ h')]
  simpa [he, zeroMult] using
    (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (analyticOn_riemannZeta _ h)).mp
      (Nat.cast_analyticOrderNatAt (zeta_order_ne_top h)).symm

end WeilExplicit
