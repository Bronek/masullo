import WeilExplicit.Growth

/-!
# Truncated Dirichlet series for zeta with a Fourier remainder

For an integer `X ≥ 1` and `Re s > 0`, `s ≠ 1`,
`ζ(s) = ∑_{n ≤ X} n^{-s} + X^{1-s}/(s-1) - s ∫_{x > X} x^{-s-1} {x} dx`.
On a vertical line the remainder integral is the Fourier integral of
`tailFun X u v = 1_{v > log X} e^{-uv} {e^v}`, whose squared `L²` norm is at most `X^{-2u}/(2u)`.

Part of a Carlson-type mean-square zero-density argument due to OpenAI Codex (E36),
formalised by Claude.
-/

namespace WeilExplicit

open Complex MeasureTheory Set

private theorem norm_tail_integrand {s : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (-s - 1) * ((Int.fract x : ℝ) : ℂ)‖ ≤ x ^ (-s.re - 1) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, sub_re, neg_re, one_re]
  apply mul_le_of_le_one_right (Real.rpow_nonneg hx.le _)
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
    using (Int.fract_lt_one x).le

theorem integrableOn_tail {s : ℂ} (hs : 0 < s.re) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ (-s - 1) * ((Int.fract x : ℝ) : ℂ)) (Ioi c) := by
  apply (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) hc).mono'
  · exact (Measurable.mul (by fun_prop : Measurable fun x : ℝ ↦ (x : ℂ) ^ (-s - 1))
      (Complex.measurable_ofReal.comp measurable_fract)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    exact norm_tail_integrand (hc.trans hx)

private theorem integral_piece {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (X : ℕ) (hX : 1 ≤ X) :
    s * ∫ x in Ioc (X : ℝ) (X + 1), (x : ℂ) ^ (-s - 1) * ((Int.fract x : ℝ) : ℂ) =
      s / (1 - s) * (((X : ℂ) + 1) ^ (1 - s) - (X : ℂ) ^ (1 - s)) +
        X * (((X : ℂ) + 1) ^ (-s) - (X : ℂ) ^ (-s)) := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  rw [integral_Ioc_eq_integral_Ioo, setIntegral_congr_fun measurableSet_Ioo
    (g := fun x : ℝ ↦ (x : ℂ) ^ (-s) - X * (x : ℂ) ^ (-s - 1)), ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith)]
  · have h0 : (0 : ℝ) ∉ uIcc (X : ℝ) (X + 1) := by
      rw [uIcc_of_le (by linarith)]; exact fun h ↦ by linarith [h.1]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      integral_cpow (Or.inr ⟨fun h ↦ hs1 (by simpa using congrArg Neg.neg h), h0⟩),
      integral_cpow (Or.inr ⟨fun h ↦ hs0 (by simpa using h), h0⟩)]
    · push_cast
      have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
      rw [show -s - 1 + 1 = -s by ring, show -s + 1 = 1 - s by ring]
      field_simp
      ring
    · exact (intervalIntegral.intervalIntegrable_cpow (Or.inr h0))
    · exact (intervalIntegral.intervalIntegrable_cpow (Or.inr h0)).const_mul _
  · intro x hx
    have hx0 : 0 < x := hX0.trans hx.1
    have hfl : ⌊x⌋ = (X : ℤ) := by
      rw [Int.floor_eq_iff]; push_cast; exact ⟨hx.1.le, hx.2⟩
    simp only [Int.fract, hfl, Int.cast_natCast, ofReal_sub, ofReal_natCast]
    have hp : (x : ℂ) ^ (-s) = (x : ℂ) ^ (-s - 1) * x := by
      conv_lhs => rw [← sub_add_cancel (-s) 1, cpow_add _ _ (ofReal_ne_zero.mpr hx0.ne'),
        cpow_one]
    rw [hp]; ring

/-- Partial summation: zeta as a truncated Dirichlet series plus a fractional-part remainder. -/
theorem zeta_eq_partial_sum {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (X : ℕ) (hX : 1 ≤ X) :
    riemannZeta s = ∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-s) + (X : ℂ) ^ (1 - s) / (s - 1) -
      s * ∫ x in Ioi (X : ℝ), (x : ℂ) ^ (-s - 1) * ((Int.fract x : ℝ) : ℂ) := by
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  have hsm1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  induction X, hX using Nat.le_induction with
  | base =>
    rw [zeta_eq_fractional_part_integral hs hs1]
    simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, one_cpow]
    field_simp
    ring
  | succ X hX ih =>
    have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
    rw [ih, ← Ioc_union_Ioi_eq_Ioi (by linarith : (X : ℝ) ≤ X + 1),
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        ((integrableOn_tail hs hX0).mono_set Ioc_subset_Ioi_self)
        (integrableOn_tail hs (by linarith)), mul_add, integral_piece hs0 hs1 X hX,
      Finset.sum_Icc_succ_top (by omega)]
    push_cast
    have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX0.ne'
    have hX1c : (X : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : (X : ℝ) + 1 ≠ 0)
    have e1 : (X : ℂ) ^ (1 - s) = X * (X : ℂ) ^ (-s) := by
      rw [sub_eq_add_neg, cpow_add _ _ hXc, cpow_one]
    have e2 : ((X : ℂ) + 1) ^ (1 - s) = ((X : ℂ) + 1) * ((X : ℂ) + 1) ^ (-s) := by
      rw [sub_eq_add_neg, cpow_add _ _ hX1c, cpow_one]
    rw [e1, e2]
    have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    field_simp
    ring

/-- The remainder integrand in the logarithmic variable, cut off below `log X`. -/
noncomputable def tailFun (X u v : ℝ) : ℂ :=
  (Ioi (Real.log X)).indicator (fun v ↦ ((Real.exp (-u * v) * Int.fract (Real.exp v) : ℝ) : ℂ)) v

private theorem ofReal_exp_cpow (v : ℝ) (w : ℂ) : ((Real.exp v : ℝ) : ℂ) ^ w = cexp (v * w) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos v).ne'),
    ← ofReal_log (Real.exp_pos v).le, Real.log_exp]

/-- On the line `Re s = u` the remainder integral is a Fourier integral of `tailFun`. -/
theorem tail_eq_fourier {X : ℝ} (hX : 0 < X) (u t : ℝ) :
    ∫ x in Ioi X, (x : ℂ) ^ (-(u + t * I) - 1) * ((Int.fract x : ℝ) : ℂ) =
      ∫ v, tailFun X u v * cexp (-(v * t) * I) := by
  rw [← Real.exp_log hX]
  rw [← integral_comp_exp_Ioi, Real.exp_log hX]
  simp_rw [tailFun, ← Set.indicator_mul_left _ _ (fun v : ℝ ↦ cexp (-(v * t) * I))]
  rw [integral_indicator measurableSet_Ioi]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ ↦ ?_
  rw [Complex.real_smul, ofReal_exp_cpow, ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  push_cast
  rw [show (v : ℂ) + v * (-(u + t * I) - 1) = -u * v + -(v * t) * I by ring, Complex.exp_add]
  ring

theorem measurable_tailFun (X u : ℝ) : Measurable (tailFun X u) :=
  (Complex.measurable_ofReal.comp ((by fun_prop : Measurable fun v : ℝ ↦ Real.exp (-u * v)).mul
    (measurable_fract.comp Real.measurable_exp))).indicator measurableSet_Ioi

theorem norm_tailFun_le (X u v : ℝ) :
    ‖tailFun X u v‖ ≤ (Ioi (Real.log X)).indicator (fun v ↦ Real.exp (-u * v)) v := by
  simp only [tailFun, indicator]
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (Int.fract_nonneg _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Int.fract_lt_one _).le
  · simp

theorem integrable_tailFun (X : ℝ) {u : ℝ} (hu : 0 < u) : Integrable (tailFun X u) := by
  refine ((integrableOn_exp_mul_Ioi (by linarith : -u < 0) (Real.log X)).integrable_indicator
    measurableSet_Ioi).mono' (measurable_tailFun X u).aestronglyMeasurable
    (.of_forall fun v ↦ norm_tailFun_le X u v)

private theorem norm_tailFun_sq_le (X u v : ℝ) :
    ‖tailFun X u v‖ ^ 2 ≤ (Ioi (Real.log X)).indicator (fun w ↦ Real.exp (-(2 * u) * w)) v := by
  have h := norm_tailFun_le X u v
  simp only [indicator] at h ⊢
  split_ifs at h ⊢
  · calc ‖tailFun X u v‖ ^ 2 ≤ Real.exp (-u * v) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = Real.exp (-(2 * u) * v) := by rw [← Real.exp_nat_mul]; ring_nf
  · simp [le_antisymm h (norm_nonneg _)]

theorem integrable_norm_tailFun_sq (X : ℝ) {u : ℝ} (hu : 0 < u) :
    Integrable fun v ↦ ‖tailFun X u v‖ ^ 2 := by
  refine ((integrableOn_exp_mul_Ioi (by linarith : -(2 * u) < 0) (Real.log X)).integrable_indicator
    measurableSet_Ioi).mono' ((measurable_tailFun X u).norm.pow_const 2).aestronglyMeasurable
    (.of_forall fun v ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact norm_tailFun_sq_le X u v

theorem integral_norm_tailFun_sq_le {X : ℝ} (hX : 0 < X) {u : ℝ} (hu : 0 < u) :
    ∫ v, ‖tailFun X u v‖ ^ 2 ≤ X ^ (-(2 * u)) / (2 * u) := by
  have hint := (integrableOn_exp_mul_Ioi (by linarith : -(2 * u) < 0) (Real.log X))
  calc ∫ v, ‖tailFun X u v‖ ^ 2
      ≤ ∫ v, (Ioi (Real.log X)).indicator (fun v ↦ Real.exp (-(2 * u) * v)) v := by
        refine integral_mono (integrable_norm_tailFun_sq X hu)
          (hint.integrable_indicator measurableSet_Ioi) fun v ↦ ?_
        exact norm_tailFun_sq_le X u v
    _ = X ^ (-(2 * u)) / (2 * u) := by
        rw [integral_indicator measurableSet_Ioi, integral_exp_mul_Ioi (by linarith),
          Real.rpow_def_of_pos hX]
        field_simp

end WeilExplicit
