import Masullo.BaezDuarte

/-!
# Controls for the Báez-Duarte criterion

`MellinBound` at `σ = 1`, where the criterion says nothing. Its proof uses `|g_N| ≤ 1`, from
`N g_N = 1 + ∑_{1 < k ≤ N} μ(k) {N / k}`.
-/

open MeasureTheory Set
open scoped ArithmeticFunction.Moebius

namespace Masullo.BaezDuarte.Controls

/-- `|g_N| ≤ 1` for `N ≥ 1`. -/
lemma abs_mobiusSum_le {N : ℕ} (hN : 0 < N) : |mobiusSum N| ≤ 1 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hsplit : ∀ k ∈ Finset.Ioc 0 N, (N : ℝ) * ((μ k : ℝ) / k) =
      (μ k : ℝ) * ((N / k : ℕ) : ℝ) + (μ k : ℝ) * Int.fract ((N : ℝ) / k) := by
    intro k _
    rw [Int.fract, ← Int.natCast_floor_eq_floor (by positivity), Nat.floor_div_eq_div,
      Int.cast_natCast]
    ring
  have h1 : ∑ k ∈ Finset.Ioc 0 N, (μ k : ℝ) * ((N / k : ℕ) : ℝ) = 1 := by
    exact sum_moebius_mul_div_real hN
  have hmem : 1 ∈ Finset.Ioc 0 N := Finset.mem_Ioc.2 ⟨one_pos, hN⟩
  have h2 : |∑ k ∈ Finset.Ioc 0 N, (μ k : ℝ) * Int.fract ((N : ℝ) / k)| ≤ N - 1 := by
    rw [← Finset.add_sum_erase _ _ hmem]
    simp only [Nat.cast_one, div_one, Int.fract_natCast, mul_zero, zero_add]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun k _ => ?_).trans ?_
    · rw [abs_mul, abs_of_nonneg (Int.fract_nonneg ((N : ℝ) / k))]
      exact mul_le_one₀ (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one)
        (Int.fract_nonneg _) (Int.fract_lt_one _).le
    · rw [Finset.sum_const, Finset.card_erase_of_mem hmem, Nat.card_Ioc, nsmul_eq_mul, mul_one,
        Nat.sub_zero, Nat.cast_sub hN, Nat.cast_one]
  have e : (N : ℝ) * mobiusSum N =
      1 + ∑ k ∈ Finset.Ioc 0 N, (μ k : ℝ) * Int.fract ((N : ℝ) / k) := by
    rw [mobiusSum, Finset.mul_sum, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, h1]
  have h3 : |(N : ℝ) * mobiusSum N| ≤ N := by
    rw [e]
    exact (abs_add_le _ _).trans (by rw [abs_one]; linarith)
  rw [abs_mul, Nat.abs_cast] at h3
  exact le_of_mul_le_mul_left (by linarith) hN'

/-- `MellinBound` holds at `σ = 1` with `C = 3`: `E_N` vanishes on `(1 / N, 1]` and is at most
`1 + 2 N ≤ 3 N` in absolute value for `N ≥ 1`. -/
theorem mellinBound_one : MellinBound 1 3 := by
  intro M
  refine ⟨max M 1, le_max_left _ _, ?_⟩
  set N := max M 1
  have hN : 0 < N := le_max_right M 1
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hb : ∀ x, |approx N x| ≤ 3 * N := fun x => by
    have := abs_approx_le N x
    have := mul_le_mul_of_nonneg_left (abs_mobiusSum_le hN) hN'.le
    linarith
  calc ∫ x in Ioc (0 : ℝ) 1, |approx N x| * x ^ ((1 : ℝ) - 1)
      ≤ ∫ x in Ioc (0 : ℝ) 1, (Iic (1 / (N : ℝ))).indicator (fun _ => 3 * (N : ℝ)) x := by
        refine setIntegral_mono_on (integrableOn_abs_approx one_pos N)
          ((integrableOn_const (by simp)).indicator measurableSet_Iic) measurableSet_Ioc
          fun x hx => ?_
        rw [sub_self, Real.rpow_zero, mul_one]
        rcases le_or_gt x (1 / N) with hxN | hxN
        · rw [indicator_of_mem (mem_Iic.2 hxN)]
          exact hb x
        · rw [approx_eq_zero hN hxN hx.2, indicator_of_notMem (by simpa using hxN)]
          simp
    _ = 3 := by
        rw [setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic,
          min_eq_right ((div_le_one hN').2 hN1), setIntegral_const, Measure.real,
          Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
        field_simp

/-- No negative constant works, for any `σ`, junk values of the integral included: the integral
is nonnegative. -/
theorem not_mellinBound_of_neg {σ C : ℝ} (hC : C < 0) : ¬ MellinBound σ C := by
  intro h
  obtain ⟨N, -, hN⟩ := h 0
  have : 0 ≤ ∫ x in Ioc (0 : ℝ) 1, |approx N x| * x ^ (σ - 1) :=
    setIntegral_nonneg measurableSet_Ioc fun x hx =>
      mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hx.1.le _)
  linarith

/-- A hypothetical zero of zeta to the right of `σ > 0` refutes `MellinBound σ C` for every `C`. -/
theorem not_mellinBound_of_zero {σ C : ℝ} (hσ : 0 < σ) {ρ : ℂ} (hρ : σ < ρ.re)
    (h0 : riemannZeta ρ = 0) : ¬ MellinBound σ C :=
  fun h => riemannZeta_ne_zero_of_mellinBound hσ h hρ h0

end Masullo.BaezDuarte.Controls
