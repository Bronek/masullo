import Masullo.Strength

/-!
# Negative controls

Each statement weakens one hypothesis of the argument behind
`Masullo.zeroSumVanishes_iff` and exhibits a counterexample.
-/

open Complex Set

namespace Masullo.Controls

/-- `eq_zero_of_hasSum_exp` fails with `∑' = 0` in place of `HasSum … 0`. -/
theorem tsum_variant_fails :
    ∃ l c : ℕ → ℂ, Function.Injective l ∧ (∀ i, (l i).re ≤ 0) ∧
      (∀ z, ∃ r > 0, ∀ i, l i ≠ z → r ≤ ‖z - l i‖) ∧
      (∀ x : ℝ, 0 ≤ x → ∑' i, c i * exp (x * l i) = 0) ∧ ∀ j, c j ≠ 0 := by
  have hinj : Function.Injective fun n : ℕ => (n : ℂ) * I := fun m n h => by
    simpa [I_ne_zero] using h
  refine ⟨fun n => n * I, fun _ => 1, hinj, by simp, ?_, ?_, by simp⟩
  · have hsep : ∀ m n : ℕ, m ≠ n → 1 ≤ ‖(m : ℂ) * I - n * I‖ := by
      intro m n h
      rw [← sub_mul, norm_mul, norm_I, mul_one]
      have : ((m : ℂ) - n) = ((m - n : ℤ) : ℂ) := by push_cast; rfl
      rw [this, norm_intCast]
      have h0 : (m - n : ℤ) ≠ 0 := by omega
      exact_mod_cast Int.one_le_abs h0
    intro z
    by_cases hz : ∃ m : ℕ, ‖z - m * I‖ < 1 / 2
    · obtain ⟨m, hm⟩ := hz
      have far : ∀ n : ℕ, n ≠ m → 1 / 2 ≤ ‖z - n * I‖ := by
        intro n hn
        have h1 := hsep m n hn.symm
        have h2 := norm_sub_le (z - n * I) (z - m * I)
        rw [sub_sub_sub_cancel_left] at h2
        linarith
      by_cases he : (m : ℂ) * I = z
      · exact ⟨1 / 2, by norm_num, fun n hn => far n fun e => hn (e ▸ he)⟩
      · have hp : 0 < ‖z - m * I‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm he))
        refine ⟨‖z - m * I‖, hp, fun n _ => ?_⟩
        by_cases e : n = m
        · rw [e]
        · linarith [far n e]
    · push Not at hz
      exact ⟨1 / 2, by norm_num, fun n _ => hz n⟩
  · intro x _
    refine tsum_eq_zero_of_not_summable fun h => ?_
    have h1 := h.tendsto_atTop_zero.norm
    have h2 : ∀ n : ℕ, ‖(1 : ℂ) * exp (x * (n * I))‖ = 1 := fun n => by
      rw [one_mul, show (x : ℂ) * (n * I) = ((x * n : ℝ) : ℂ) * I by push_cast; ring,
        norm_exp_ofReal_mul_I]
    simp only [h2, norm_zero] at h1
    exact zero_ne_one (tendsto_nhds_unique h1 tendsto_const_nhds)

/-- The translates of one test function by multiples of `2π` do not separate the points `0` and
`i`: a nonzero weighting of these points annihilates all of them. -/
theorem discrete_translates_fail :
    ∃ (φ : TestFunction) (l w : Fin 2 → ℂ), Function.Injective l ∧ w ≠ 0 ∧
      ∀ k : ℕ, HasSum
        (fun i => w i * (φ.translate (2 * Real.pi * k) (by positivity)).hat (l i)) 0 := by
  obtain ⟨φ, hφ⟩ := TestFunction.exists_hat_ne_zero 0
  refine ⟨φ, ![0, I], ![φ.hat I, -φ.hat 0], ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [I_ne_zero, I_ne_zero.symm]
  · intro h
    exact hφ (by simpa using congrFun h 1)
  · intro k
    have e : exp ((2 * Real.pi * k : ℝ) * I) = 1 := by
      rw [← exp_nat_mul_two_pi_mul_I k]
      congr 1
      push_cast
      ring
    have hs := hasSum_fintype
      fun i => (![φ.hat I, -φ.hat 0] : Fin 2 → ℂ) i *
        (φ.translate (2 * Real.pi * k) (by positivity)).hat ((![0, I] : Fin 2 → ℂ) i)
    convert hs using 1
    symm
    simp only [Fin.sum_univ_two, TestFunction.hat_translate, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_zero, Complex.exp_zero, e]
    ring

end Masullo.Controls
