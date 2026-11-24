import WeilExplicit.GammaIntegral
import WeilExplicit.ZeroRectangle
import WeilExplicit.GoodHeights

/-! # The completed contour at the sequence of good heights -/

namespace WeilExplicit

open WeilExplicit (weight)

open Complex Real Filter Set MeasureTheory
open scoped Topology

/-- Reflection extends the good horizontal estimate across the whole rectangle. -/
theorem completed_good_sequence : ∃ (T : ℕ → ℝ) (K : ℝ), Tendsto T atTop atTop ∧
    ∀ j, 1 ≤ T j ∧
      (∀ s : ℂ, |s.im| = T j → 1/2 ≤ s.re → s.re ≤ 2 → riemannZeta s ≠ 0) ∧
      ∀ s : ℂ, |s.im| = T j → -1 ≤ s.re → s.re ≤ 2 → ‖logDeriv completedRiemannZeta s‖ ≤ K*T j := by
  obtain ⟨C,hC,h⟩ := good_heights
  choose T hlo _hhi hgood using fun n : ℕ ↦ h (n+7) (by omega)
  obtain ⟨A,hA,hg⟩ := gamma_strip_bound
  refine ⟨T,2*A+16*C,tendsto_atTop_mono (fun n ↦ ?_) (tendsto_natCast_atTop_atTop (R := ℝ)),
    fun n ↦ ?_⟩
  · exact (show (n:ℝ) ≤ ((n+7:ℕ):ℝ) by push_cast; linarith).trans (hlo n)
  have hN := hlo n
  push_cast at hN
  have hT : 1 ≤ T n := by linarith [Nat.cast_nonneg (α := ℝ) n]
  refine ⟨hT,fun s ht ha hb ↦ (hgood n s ht ha hb).1,fun s ht ha hb ↦ ?_⟩
  have hright (z : ℂ) (hz : |z.im| = T n) (hl : 1/2 ≤ z.re) (hr : z.re ≤ 2) :
      ‖logDeriv completedRiemannZeta z‖ ≤ (2*A+16*C)*T n := by
    obtain ⟨hn,hd⟩ := hgood n z hz hl hr
    have hz₁ : z ≠ 1 := fun e ↦ by simp [e] at hz; linarith
    rw [logDeriv_completed_split (by linarith) hz₁ hn]
    apply (norm_add_le ..).trans
    have hΓ := hg z hl hr
    rw [hz] at hΓ
    push_cast at hd
    let x := (n:ℝ)+7+3
    have hx : 1 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hlog := Real.log_le_rpow_div (zero_le_one.trans hx) (by norm_num : (0:ℝ) < 1/2)
    rw [← sqrt_eq_rpow] at hlog
    have hsq : Real.log x ^ 2 ≤ 4*x := by
      nlinarith [sq_le_sq' (by linarith [sqrt_nonneg x, Real.log_nonneg hx] : -(2*√x) ≤ Real.log x)
        (by linarith : Real.log x ≤ 2*√x), Real.sq_sqrt (zero_le_one.trans hx)]
    have hx' : 4*x ≤ 16*T n := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) n]
    change ‖logDeriv riemannZeta z‖ ≤ C*(Real.log x)^2 at hd
    nlinarith [mul_le_mul_of_nonneg_left (hsq.trans hx') hC.le,
      mul_le_mul_of_nonneg_left (WeilExplicit.sqrt_one_add_le_two_mul hT) hA]
  by_cases he : 1/2 ≤ s.re
  · exact hright s ht he hb
  · have hs₀ : s ≠ 0 := fun e ↦ by simp [e] at ht; linarith
    have hs₁ : s ≠ 1 := fun e ↦ by simp [e] at ht; linarith
    have h' := hright (1-s) (by simpa using ht) (by simp; linarith) (by simp; linarith)
    simpa [logDeriv_completed_one_sub hs₀ hs₁] using h'

/-- On Re s = 2, quadratic weight decay makes the zeta logarithmic derivative integrable. -/
theorem integrable_zeta_line {W : ℂ → ℂ} (hw : Continuous W) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖W z‖ ≤ M/(1+z.im^2)) :
    Integrable (fun t : ℝ ↦ W (2+t*I) * logDeriv riemannZeta (2+t*I)) := by
  obtain ⟨B,hB,hb⟩ := bounded_logDeriv_zeta_line (c := 2) (by norm_num)
  apply integrable_line_mul (c := 2) hM hB hw
  · intro t
    exact (analyticAt_logDeriv_zeta (by norm_num)).continuousAt
  · intro t
    simpa using h (2+t*I) (by norm_num) (by norm_num)
  · intro t
    exact (hb t).trans (le_mul_of_one_le_right hB (WeilExplicit.sqrt_one_add_abs_ge_one t))

/-- On Re s = 2, the completed logarithmic derivative splits into its Gamma and zeta terms. -/
protected theorem completed_split_two (t : ℝ) : logDeriv completedRiemannZeta (2+t*I) =
    logDeriv Gammaℝ (2+t*I) + logDeriv riemannZeta (2+t*I) := by
  apply logDeriv_completed_split (by norm_num)
  · intro e
    have := congrArg Complex.re e
    norm_num at this
  · apply riemannZeta_ne_zero_of_one_le_re
    norm_num

private theorem integrable_completed_line {W : ℂ → ℂ} (hw : Continuous W) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖W z‖ ≤ M/(1+z.im^2)) :
    Integrable (fun t : ℝ ↦ W (2+t*I) * logDeriv completedRiemannZeta (2+t*I)) := by
  simp_rw [WeilExplicit.completed_split_two, mul_add]
  exact (integrable_gamma_line hw hM h (x := 2) (by norm_num) le_rfl).add
    (integrable_zeta_line hw hM h)

/-- The zero sum is evaluated by the full paired integral on Re s = 2. -/
theorem completed_contour {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hs : HasCompactSupport k) :
    (2*(π:ℂ)) * ((∑' ρ : stripZeros, (zeroMult ρ : ℂ) * weight k ρ) - weight k 0 - weight k 1) =
      ∫ t : ℝ, pairedWeight k (2+t*I) * logDeriv completedRiemannZeta (2+t*I) := by
  let W := weight k
  let D := logDeriv completedRiemannZeta
  let f (z : ℂ) := W z * D z
  let g (t : ℝ) := W (1-(2+t*I)) * D (2+t*I)
  obtain ⟨M,hM,h⟩ := weight_strip_decay hk hs
  obtain ⟨N,hN,hn⟩ := reflected_weight_strip_decay hk hs
  have hw := differentiable_weight hk.continuous hs
  have hr : Integrable (fun t : ℝ ↦ f (2+t*I)) := integrable_completed_line hw.continuous hM h
  have hg : Integrable g := integrable_completed_line (W := fun z ↦ W (1-z))
    (hw.continuous.comp (by fun_prop)) hN hn
  have left (t : ℝ) : f (-1+t*I) = -g (-t) := by
    have e : (-1:ℂ)+t*I = 1-(2+(-t:ℝ)*I) := by push_cast; ring
    dsimp [f,g,D]
    rw [e, logDeriv_completed_one_sub]
    · ring
    all_goals intro e'; have he := congrArg Complex.re e'; norm_num at he
  have hl : Integrable (fun t : ℝ ↦ f (-1+t*I)) := by
    simp_rw [left]
    simpa using (hg.comp_mul_left' (show (-1:ℝ) ≠ 0 by norm_num)).neg
  obtain ⟨T,K,ht,hgood⟩ := completed_good_sequence
  have hsides (j : ℕ) (z : ℂ) (hz : z.re ∈ uIcc (-1:ℝ) 2) (hh : |z.im| = T j) :
      ‖f z‖ ≤ M*K/T j := by
    rw [uIcc_of_le (by norm_num)] at hz
    exact WeilExplicit.horizontal_product_bound (W := W z) (D := D z) hM
      (zero_lt_one.trans_le (hgood j).1)
      (by simpa only [← hh, sq_abs] using h z hz.1 hz.2) ((hgood j).2.2 z hh hz.1 hz.2)
  have hc := rectIntegral_tendsto (f := f) (a := -1) (b := 2) ht
    (by simpa only [ofReal_neg,ofReal_one] using hl) (by simpa only [ofReal_ofNat] using hr)
    (B := M*K) (Eventually.of_forall hsides)
  have hsum := (summable_zero_transform hk hs).hasSum.comp (tendsto_zeroWindow.comp ht)
  have hres (j : ℕ) := completed_rectangle hw (zero_lt_one.trans_le (hgood j).1) (hgood j).2.1
  simp_rw [show ∀ j, rectIntegral f (-1) 2 (-T j) (T j) = _ from hres] at hc
  have he := tendsto_nhds_unique (((hsum.sub_const (W 0)).sub_const (W 1)).const_mul (2*(π:ℂ)*I)) hc
  simp only [ofReal_ofNat, ofReal_neg, ofReal_one] at he
  change (2*(π:ℂ)*I)*((∑' ρ : stripZeros, (zeroMult ρ : ℂ)*W ρ) - W 0 - W 1) =
    I*(∫ t : ℝ, f (2+t*I)) - I*(∫ t : ℝ, f (-1+t*I)) at he
  simp_rw [left] at he
  rw [integral_neg, integral_neg_eq_self] at he
  change (2*(π:ℂ))*((∑' ρ : stripZeros, (zeroMult ρ : ℂ)*W ρ)-W 0-W 1) = _
  simp only [pairedWeight, add_mul]
  rw [integral_add hr hg]
  apply mul_left_cancel₀ I_ne_zero
  linear_combination he

end WeilExplicit
