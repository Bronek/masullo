import Masullo.ExplicitFormula
import Masullo.Synthesis.Duality

/-!
# Controls

Each negative control drops or weakens one hypothesis and exhibits a counterexample. Two concern the
argument behind `Masullo.zeroSumVanishes_iff`, one the duality theorem behind spectral synthesis.
The positive control shows that the inner expansion is satisfiable.
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
lemma continuous_hat (φ : TestFunction) : Continuous φ.hat := φ.continuous_hat

/-- The translates of one test function by multiples of a fixed step do not separate all points:
a nonzero weighting of two points, at neither of which the Mellin transform vanishes, annihilates
all of them. -/
theorem discrete_translates_fail :
    ∃ (φ : TestFunction) (x : ℝ) (hx : 0 < x) (l w : Fin 2 → ℂ), Function.Injective l ∧
      (∀ i, w i ≠ 0) ∧ (∀ i, φ.hat (l i) ≠ 0) ∧
      ∀ k : ℕ, HasSum (fun i => w i * (φ.translate (k * x) (by positivity)).hat (l i)) 0 := by
  obtain ⟨φ, -, hφ⟩ :=
    TestFunction.exists_nonneg_hat_ne_zero_on ((countable_singleton (0 : ℂ)).insert I)
  refine ⟨φ, 2 * Real.pi, by positivity, ![0, I], ![φ.hat I, -φ.hat 0], ?_, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [I_ne_zero, I_ne_zero.symm]
  · intro i
    fin_cases i <;> simp [hφ]
  · intro i
    fin_cases i <;> simp [hφ]
  · intro k
    have e : exp (((k * (2 * Real.pi) : ℝ) : ℂ) * I) = 1 := by
      rw [← exp_nat_mul_two_pi_mul_I k]
      push_cast
      ring_nf
    have hs := hasSum_fintype fun i => (![φ.hat I, -φ.hat 0] : Fin 2 → ℂ) i *
      (φ.translate (k * (2 * Real.pi)) (by positivity)).hat ((![0, I] : Fin 2 → ℂ) i)
    convert hs using 1
    symm
    simp only [Fin.sum_univ_two, TestFunction.hat_translate, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_zero, Complex.exp_zero, e]
    ring

/-- The inner expansion holds at widths above `1/2`, where it carries no information. -/
theorem innerExpansion_of_half_lt {a : ℝ} (ha : 1 / 2 < a) : InnerExpansion a := by
  rw [innerExpansion_iff]
  rintro ⟨ρ, hz, h0, h1, h⟩
  exact ((abs_sub_half_lt_half ⟨hz, h0, h1⟩).trans ha).not_ge h

/-- Transform of a modulated indicator of `(0, 1]`. -/
lemma jet_window (c z : ℂ) (h : z ≠ c) :
    Synthesis.jet ((Ioc (0 : ℝ) 1).indicator fun x => exp (-c * x)) 0 z =
      (exp (z - c) - 1) / (z - c) := by
  have e : ∀ x : ℝ, (Ioc (0 : ℝ) 1).indicator (fun x : ℝ => exp (-c * x)) x * exp (z * x) =
      (Ioc (0 : ℝ) 1).indicator (fun x : ℝ => exp ((z - c) * x)) x := fun x => by
    by_cases hx : x ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem hx, indicator_of_mem hx, ← Complex.exp_add]
      ring_nf
    · simp [indicator_of_notMem hx]
  simp only [Synthesis.jet_zero, e]
  rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    integral_exp_mul_complex (sub_ne_zero.2 h)]
  simp

/-- `Synthesis.integral_eq_zero_of_order_le` fails without its hypothesis on orders: for every real
`c` in the strip there is a counterexample at an exponent with real part `c`. -/
theorem order_hypothesis_needed {a c : ℝ} (hc : |c| < a) : ∃ (z₀ : ℂ) (h u : ℝ → ℂ), z₀.re = c ∧
    Synthesis.Rapid h ∧ Synthesis.Dual a (fun x => exp (z₀ * x)) u ∧
    (∃ b > a, ∀ ε > 0, ∀ R : ℝ, ∃ T ≥ R, ∀ z : ℂ, |z.im| = T → |z.re| ≤ b →
      Real.exp (-ε * T ^ 2) ≤ ‖Synthesis.jet h 0 z‖) ∧
    (∀ t, Synthesis.cross (fun x => exp (z₀ * x)) h t = 0) ∧
    Synthesis.jet h 0 z₀ = 0 ∧ ∫ x : ℝ, exp (z₀ * x) * u x ≠ 0 := by
  have ha := (abs_nonneg c).trans_lt hc
  set z₀ : ℂ := c + 2 * Real.pi * I
  have hre : z₀.re = c := by simp [z₀]
  have hne : z₀ ≠ c := by simp [z₀, Real.pi_ne_zero]
  have hm : ∀ w : ℂ, AEStronglyMeasurable ((Ioc (0 : ℝ) 1).indicator fun x => exp (-w * x)) :=
    fun w => (by fun_prop : Continuous fun x : ℝ => exp (-w * x)).aestronglyMeasurable.indicator
      measurableSet_Ioc
  have hX : Synthesis.jet ((Ioc (0 : ℝ) 1).indicator fun x => exp (-(c : ℂ) * x)) 0 z₀ = 0 := by
    rw [jet_window _ _ hne, add_sub_cancel_left, exp_two_pi_mul_I, sub_self, zero_div]
  refine ⟨z₀, _, (Ioc (0 : ℝ) 1).indicator fun x => exp (-z₀ * x), hre, ⟨hm c, fun b => ?_⟩,
    ⟨?_, ?_⟩, ⟨a + 1, by linarith, fun ε hε R => ?_⟩, fun t => ?_, hX, ?_⟩
  · refine ⟨Real.exp (|c| + |b|), fun x => ?_⟩
    by_cases hx : x ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem hx, norm_exp, ← Real.exp_add, Real.exp_le_exp, abs_of_pos hx.1]
      simp only [neg_mul, neg_re, re_ofReal_mul, ofReal_re]
      nlinarith [neg_abs_le c, le_abs_self b, abs_nonneg b, abs_nonneg c, hx.1, hx.2]
    · rw [indicator_of_notMem hx, norm_zero]
      positivity
  · have hcont : Continuous fun x : ℝ => (Real.exp (-a * |x|) : ℂ) * exp (z₀ * x) := by fun_prop
    refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2
      ((Synthesis.integrable_exp_neg_mul_abs (sub_pos.2 hc)).mono' (by fun_prop)
        (Eventually.of_forall fun x => ?_))
    rw [Real.norm_of_nonneg (by positivity), norm_mul, norm_real, norm_exp,
      Real.norm_of_nonneg (Real.exp_pos _).le, re_mul_ofReal, hre, ← Real.exp_add,
      ← Real.exp_nat_mul, Real.exp_le_exp]
    have h1 : c * x ≤ |c| * |x| := (le_abs_self _).trans (abs_mul c x).le
    push_cast
    nlinarith [mul_nonneg (sub_pos.2 hc).le (abs_nonneg x)]
  · have e : (fun x : ℝ => (Real.exp (a * |x|) : ℂ) *
        (Ioc (0 : ℝ) 1).indicator (fun x : ℝ => exp (-z₀ * x)) x) =
        (Ioc (0 : ℝ) 1).indicator fun x : ℝ => (Real.exp (a * |x|) : ℂ) * exp (-z₀ * x) :=
      funext fun x =>
        (indicator_mul_right _ (fun x : ℝ => (Real.exp (a * |x|) : ℂ)) _).symm
    rw [e, memLp_indicator_iff_restrict measurableSet_Ioc]
    have hcont : Continuous fun x : ℝ => (Real.exp (a * |x|) : ℂ) * exp (-z₀ * x) := by fun_prop
    exact (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2
      ((hcont.norm.pow 2).integrableOn_Ioc)
  · obtain ⟨n, hn⟩ := exists_nat_ge (max R ((2 * a + 2) / ε))
    have hT : (n : ℝ) ≤ n * (2 * Real.pi) + Real.pi := by
      nlinarith [Real.pi_gt_three, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    refine ⟨n * (2 * Real.pi) + Real.pi, (le_max_left _ _).trans (hn.trans hT), fun z hi hr => ?_⟩
    have hcos : Real.cos z.im = -1 := by
      rw [← Real.cos_abs, hi, Real.cos_nat_mul_two_pi_add_pi]
    have hT1 : 1 ≤ n * (2 * Real.pi) + Real.pi := by
      nlinarith [Real.pi_gt_three, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    generalize n * (2 * Real.pi) + Real.pi = T at hi hT hT1
    have hne : z ≠ c := by
      rintro rfl
      simp at hi
      linarith
    have h1 : 1 ≤ ‖exp (z - c) - 1‖ := by
      refine le_trans ?_ (abs_re_le_norm _)
      rw [sub_re, exp_re, sub_im, ofReal_im, sub_zero, hcos, one_re, abs_of_neg] <;>
        linarith [Real.exp_pos (z - c).re]
    have h2 : ‖z - c‖ ≤ 2 * a + 1 + T := by
      have := norm_le_abs_re_add_abs_im (z - c)
      have h3 := abs_sub z.re c
      simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero, hi] at this
      linarith
    have h3 : 2 * a + 1 + T ≤ Real.exp (ε * T ^ 2) := by
      have h4 := (div_le_iff₀ hε).1 (((le_max_right _ _).trans hn).trans hT)
      nlinarith [Real.add_one_le_exp (ε * T ^ 2)]
    rw [jet_window _ _ hne, norm_div, neg_mul, Real.exp_neg, ← one_div]
    have := norm_pos_iff.2 (sub_ne_zero.2 hne)
    gcongr
    linarith
  · rw [Synthesis.cross_exp, hX, mul_zero]
  · have e : ∀ x : ℝ, exp (z₀ * x) * (Ioc (0 : ℝ) 1).indicator (fun x => exp (-z₀ * x)) x =
        (Ioc (0 : ℝ) 1).indicator (fun _ => 1) x := fun x => by
      by_cases hx : x ∈ Ioc (0 : ℝ) 1
      · rw [indicator_of_mem hx, indicator_of_mem hx, ← Complex.exp_add]
        simp
      · simp [indicator_of_notMem hx]
    simp only [e]
    rw [integral_indicator measurableSet_Ioc]
    simp

end Masullo.Controls
