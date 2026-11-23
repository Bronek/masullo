import Masullo.Strength

/-!
# Negative controls

Each statement weakens one hypothesis of the argument behind
`Masullo.zeroSumVanishes_iff` and exhibits a counterexample.
-/

open Complex Set Filter Topology MeasureTheory

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

/-- The Mellin transform of a test function is continuous. -/
lemma continuous_hat (φ : TestFunction) : Continuous φ.hat := by
  have hloc : LocallyIntegrableOn φ.toFun (Ioi 0) :=
    φ.contDiff.continuous.locallyIntegrable.locallyIntegrableOn _
  have htop : φ.toFun =ᶠ[atTop] fun _ => 0 := by
    obtain ⟨R, hR⟩ := φ.hasCompactSupport.isCompact.bddAbove
    filter_upwards [eventually_gt_atTop R] with t ht
    exact image_eq_zero_of_notMem_tsupport fun h => absurd (hR h) (not_le.2 ht)
  have hbot : φ.toFun =ᶠ[𝓝[>] 0] fun _ => 0 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (zero_lt_one (α := ℝ)))] with t ht
    exact image_eq_zero_of_notMem_tsupport fun h =>
      lt_asymm (mem_Iio.1 ht) (mem_Ioi.1 (φ.tsupport_subset h))
  refine continuous_iff_continuousAt.2 fun z => ?_
  exact (mellin_differentiableAt_of_isBigO_rpow hloc
    (htop.trans_isBigO (Asymptotics.isBigO_zero _ _)) (lt_add_one z.re)
    (hbot.trans_isBigO (Asymptotics.isBigO_zero _ _)) (sub_one_lt z.re)).continuousAt

/-- The translates of one test function by multiples of a fixed step do not separate all points:
a nonzero weighting of two points, at neither of which the Mellin transform vanishes, annihilates
all of them. -/
theorem discrete_translates_fail :
    ∃ (φ : TestFunction) (x : ℝ) (hx : 0 < x) (l w : Fin 2 → ℂ), Function.Injective l ∧
      (∀ i, w i ≠ 0) ∧ (∀ i, φ.hat (l i) ≠ 0) ∧
      ∀ k : ℕ, HasSum (fun i => w i * (φ.translate (k * x) (by positivity)).hat (l i)) 0 := by
  obtain ⟨φ, hφ⟩ := TestFunction.exists_hat_ne_zero 0
  have hlim : Tendsto (fun x : ℝ => ((2 * Real.pi / x : ℝ) : ℂ) * I) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := 2 * Real.pi)).div_atTop (tendsto_id (α := ℝ))
    simpa using ((continuous_ofReal.tendsto 0).comp h).mul_const I
  have hev := hlim.eventually ((continuous_hat φ).continuousAt.eventually_ne hφ)
  obtain ⟨x, hx1, hx⟩ := (hev.and (eventually_gt_atTop 0)).exists
  have hq : ((2 * Real.pi / x : ℝ) : ℂ) * I ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.2 (by positivity)) I_ne_zero
  set q : ℂ := ((2 * Real.pi / x : ℝ) : ℂ) * I with hqdef
  refine ⟨φ, x, hx, ![0, q], ![φ.hat q, -φ.hat 0], ?_, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [hq, hq.symm]
  · intro i
    fin_cases i <;> simp [hφ, hx1]
  · intro i
    fin_cases i <;> simp [hφ, hx1]
  · intro k
    have e : exp (((k * x : ℝ) : ℂ) * q) = 1 := by
      rw [← exp_nat_mul_two_pi_mul_I k, hqdef]
      congr 1
      have : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
      push_cast
      field_simp
    have hs := hasSum_fintype fun i => (![φ.hat q, -φ.hat 0] : Fin 2 → ℂ) i *
      (φ.translate (k * x) (by positivity)).hat ((![0, q] : Fin 2 → ℂ) i)
    convert hs using 1
    symm
    simp only [Fin.sum_univ_two, TestFunction.hat_translate, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_zero, Complex.exp_zero, e]
    ring

end Masullo.Controls
