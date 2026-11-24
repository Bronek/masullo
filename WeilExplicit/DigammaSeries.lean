import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # The partial-fraction series for the digamma function -/

namespace WeilExplicit

open Complex Filter Metric Set
open scoped Topology

private noncomputable def logTerm (n : ℕ) (s : ℂ) :=
  (s-1)/(n+1) + log (n+1 : ℂ) - log (s+n)

private noncomputable def psiTerm (n : ℕ) (s : ℂ) := (n+1 : ℂ)⁻¹ - (s+n)⁻¹

private theorem logTerm_deriv (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (logTerm n) (psiTerm n s) s := by
  have h : s + n ∈ slitPlane := Or.inl (by simp; positivity)
  unfold logTerm psiTerm
  simpa [one_div, Function.comp_def, Pi.sub_def] using!
    (((((hasDerivAt_id s).sub_const 1).div_const (n+1 : ℂ)).add_const (log (n+1 : ℂ))).sub
      ((hasDerivAt_log h).comp s ((hasDerivAt_id s).add_const (n : ℂ))))

private theorem norm_psiTerm {s : ℂ} {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1) (hs : a ≤ s.re) (n : ℕ) :
    ‖psiTerm n s‖ ≤ (‖s-1‖ / a) / (n+1 : ℝ)^2 := by
  have hpos : 0 < (s+n).re := by simp; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hn : s+n ≠ 0 := fun h ↦ by simp [h] at hpos
  have hm : (n+1 : ℂ) ≠ 0 := by exact_mod_cast (show (n : ℝ)+1 ≠ 0 by positivity)
  have heq : psiTerm n s = (s-1)/((n+1)*(s+n)) := by unfold psiTerm; field_simp; ring
  have hlow : a*((n : ℝ)+1) ≤ ‖s+n‖ := by
    apply le_trans _ (re_le_norm _)
    simp only [add_re, natCast_re]
    nlinarith [mul_le_mul_of_nonneg_right ha' (Nat.cast_nonneg (α := ℝ) n)]
  rw [heq, norm_div, norm_mul, show ‖(n+1 : ℂ)‖ = (n : ℝ)+1 by
    exact_mod_cast Complex.norm_natCast (n+1)]
  calc
    _ ≤ ‖s-1‖ / (((n : ℝ)+1) * (a*((n : ℝ)+1))) := by gcongr
    _ = _ := by field_simp

private theorem logSeries_spec {s : ℂ} (hs : 0 < s.re) :
    Summable (logTerm · s) ∧ HasDerivAt (fun z ↦ ∑' n, logTerm n z) (∑' n, psiTerm n s) s := by
  let a := min s.re 1 / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have ha' : a < 1 := by dsimp [a]; linarith [min_le_right s.re 1]
  have has : a < s.re := by dsimp [a]; linarith [min_le_left s.re 1]
  let R := ‖s‖+2
  let U := ball (0 : ℂ) R ∩ {z : ℂ | a < z.re}
  have hU : IsOpen U := isOpen_ball.inter (isOpen_lt continuous_const continuous_re)
  have hc : IsPreconnected U :=
    ((convex_ball (0 : ℂ) R).inter (convex_halfSpace_re_gt a)).isPreconnected
  have h1 : 1 ∈ U := ⟨by simpa [R] using (show 1 < ‖s‖ + 2 by linarith [norm_nonneg s]),
    by simpa using ha'⟩
  have hmem : s ∈ U := ⟨by simp [R], has⟩
  let M := (R+1)/a
  have hsum : Summable (fun n : ℕ ↦ M / (n+1 : ℝ)^2) := by
    simpa [div_eq_mul_inv] using (((summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))).mul_left M)
  have hb (n : ℕ) (z : ℂ) (hz : z ∈ U) : ‖psiTerm n z‖ ≤ M/(n+1 : ℝ)^2 := by
    apply (norm_psiTerm ha ha'.le hz.2.le _).trans
    have hr := mem_ball_zero_iff.mp hz.1
    dsimp [M]
    gcongr
    simpa using (norm_sub_le z 1).trans (add_le_add hr.le le_rfl)
  have hd (n : ℕ) (z : ℂ) (hz : z ∈ U) := logTerm_deriv n (ha.trans hz.2)
  have h₀ : Summable (logTerm · 1) := by simp [logTerm, add_comm]
  exact ⟨summable_of_summable_hasDerivAt_of_isPreconnected hsum hU hc hd hb h1 h₀ hmem,
    hasDerivAt_tsum_of_isPreconnected hsum hU hc hd hb h1 h₀ hmem⟩

private theorem exp_partial_logTerm (s : ℂ) (hs : 0 < s.re) (N : ℕ) :
    exp (∑ n ∈ Finset.range N, logTerm n s) =
      exp ((s-1) * (harmonic N : ℂ)) * (N.factorial : ℂ) / ∏ n ∈ Finset.range N, (s+n) := by
  induction N with
  | zero => simp [harmonic_zero]
  | succ N ih =>
    have hn : s+N ≠ 0 := fun h ↦ by
      have : 0 < (s+N).re := by simp; positivity
      simp [h] at this
    have hk : (N+1 : ℂ) ≠ 0 := by exact_mod_cast (show (N : ℝ)+1 ≠ 0 by positivity)
    rw [Finset.sum_range_succ, exp_add, ih, Nat.factorial_succ, harmonic_succ,
      Finset.prod_range_succ]
    push_cast
    simp only [logTerm, exp_sub, exp_add, exp_log hk, exp_log hn, mul_add, div_eq_mul_inv]
    rw [← mul_add (∏ n ∈ Finset.range N, (s+n)) s (N : ℂ), mul_inv_rev]
    ring

private theorem exp_logSeries {s : ℂ} (hs : 0 < s.re) :
    exp (∑' n, logTerm n s) = exp ((s-1)*(Real.eulerMascheroniConstant : ℂ)) * Gamma s := by
  have h := ((logSeries_spec hs).1.hasSum.tendsto_sum_nat).cexp
  have hγ := (continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log
  have hratio : Tendsto (fun n : ℕ ↦ 1 + s / (n : ℂ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat s)
  have H := (((hγ.const_mul (s-1)).cexp.mul hratio).mul (GammaSeq_tendsto_Gamma s))
  apply tendsto_nhds_unique h
  apply (show _ from (by simpa using H : Tendsto _ atTop (𝓝 _))).congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hz : s+n ≠ 0 := fun h ↦ by
    have : 0 < (s+n).re := by simp; positivity
    simp [h] at this
  rw [exp_partial_logTerm _ hs, GammaSeq, Finset.prod_range_succ]
  simp only [mul_sub, exp_sub, cpow_def_of_ne_zero hn', sub_mul]
  simp only [one_mul, exp_log hn', mul_comm (log (n : ℂ)) s]
  field_simp
  ring

/-- Euler's partial-fraction expansion of the digamma function on the right half-plane. -/
theorem digamma_hasSum {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun n : ℕ ↦ (n+1 : ℂ)⁻¹ - (s+n)⁻¹) (digamma s + Real.eulerMascheroniConstant) := by
  let γ : ℂ := Real.eulerMascheroniConstant
  have hsum : Summable (psiTerm · s) := by
    let a := min s.re 1
    have ha : 0 < a := lt_min hs zero_lt_one
    apply Summable.of_norm_bounded (g := fun n : ℕ ↦ (‖s-1‖/a)/(n+1 : ℝ)^2) ?_
      (norm_psiTerm ha (min_le_right ..) (min_le_left ..))
    simpa [div_eq_mul_inv] using (((summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))).mul_left (‖s-1‖/a))
  have hΓ := differentiableAt_Gamma (s := s) (fun n h ↦ by simp [h] at hs; linarith)
  have hn := Gamma_ne_zero_of_re_pos hs
  have heq : (fun z ↦ exp (∑' n, logTerm n z)) =ᶠ[𝓝 s] fun z ↦ exp ((z-1)*γ) * Gamma z := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
      using exp_logSeries hz
  have hD := ((logSeries_spec hs).2.cexp.congr_of_eventuallyEq heq.symm).deriv
  have hE := (((((hasDerivAt_id s).sub_const 1).mul_const γ).cexp).mul hΓ.hasDerivAt).deriv
  rw [exp_logSeries hs] at hD
  have h := hD.symm.trans hE
  change HasSum (psiTerm · s) _
  rw [hsum.hasSum_iff]
  simp only [digamma, logDeriv_apply]
  change _ = _ + γ
  field_simp [hn]
  apply mul_left_cancel₀ (exp_ne_zero ((s-1)*γ))
  dsimp [γ] at h ⊢
  linear_combination h

private theorem inverse_square_tail (N : ℕ) (hN : 0 < N) :
    ∑' k : ℕ, 1 / ((k+N : ℕ) + 1 : ℝ)^2 ≤ 1 / (N : ℝ) := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  let f (x : ℝ) := x ^ (-2 : ℝ)
  have ha : AntitoneOn f (Ici (N : ℝ)) := fun x hx y _ hxy ↦
    Real.rpow_le_rpow_of_nonpos (hN'.trans_le hx) hxy (by norm_num)
  have h := ha.tsum_comp_add_le_integral N
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hN')
      (fun x hx ↦ Real.rpow_nonneg (hN'.trans hx).le _)
  dsimp only [f] at h
  rw [integral_Ioi_rpow_of_lt (by norm_num) hN'] at h
  norm_num [Real.rpow_neg, one_div] at h ⊢
  exact h

/-- A logarithmic bound away from the poles, obtained by splitting Euler's
series at the first integer above the distance to one. -/
theorem norm_digamma_le {s : ℂ} (hs : 1/4 ≤ s.re) :
    ‖digamma s‖ ≤ 10 + 5 * Real.log (‖s-1‖ + 2) := by
  let N := ⌈‖s-1‖⌉₊ + 1
  have hN : 0 < N := Nat.succ_pos _
  have hN' : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hle : ‖s-1‖ ≤ (N : ℝ) := by dsimp [N]; push_cast; linarith [Nat.le_ceil ‖s-1‖]
  have hupper : (N : ℝ) ≤ ‖s-1‖ + 2 := by
    dsimp [N]; push_cast; linarith [Nat.ceil_lt_add_one (norm_nonneg (s-1))]
  have H := digamma_hasSum (by linarith : 0 < s.re)
  change HasSum (psiTerm · s) _ at H
  have hsplit := H.summable.sum_add_tsum_nat_add N
  rw [H.tsum_eq] at hsplit
  have hhead : ‖∑ n ∈ Finset.range N, psiTerm n s‖ ≤ 5 * (harmonic N : ℝ) := by
    refine (norm_sum_le ..).trans ?_
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Nat.cast_add_one,
      Rat.cast_add, Rat.cast_one, Rat.cast_natCast, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    have hb : ((n : ℝ)+1)/4 ≤ ‖s + n‖ := by
      have := re_le_norm (s+n)
      simp only [add_re, natCast_re] at this
      linarith [Nat.cast_nonneg (α := ℝ) n]
    apply (norm_sub_le _ _).trans
    rw [norm_inv, norm_inv, show ‖(n+1 : ℂ)‖ = (n : ℝ)+1 by
      exact_mod_cast Complex.norm_natCast (n+1)]
    have hh := inv_anti₀ (by positivity : 0 < ((n : ℝ)+1)/4) hb
    rw [inv_div] at hh
    linarith only [show ‖s+(n:ℂ)‖⁻¹ ≤ 4*((n:ℝ)+1)⁻¹ by simpa [div_eq_mul_inv] using hh]
  have htail : ‖∑' k, psiTerm (k+N) s‖ ≤ 4 := by
    have hu := (summable_nat_add_iff N).mpr H.summable
    have hv : Summable (fun k : ℕ ↦ (‖s-1‖/(1/4)) / (((k+N : ℕ) : ℝ)+1)^2) := by
      apply (summable_nat_add_iff (f := fun k : ℕ ↦ (‖s-1‖/(1/4)) / ((k : ℝ)+1)^2) N).mpr
      simpa [div_eq_mul_inv] using (((summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))).mul_left (‖s-1‖/(1/4 : ℝ)))
    apply (norm_tsum_le_tsum_norm hu.norm).trans
    apply (hu.norm.tsum_le_tsum
      (fun k ↦ norm_psiTerm (by norm_num) (by norm_num) hs (k+N)) hv).trans
    simp_rw [div_eq_mul_one_div (‖s-1‖ / (1/4))]
    rw [tsum_mul_left]
    have := mul_le_mul_of_nonneg_left (inverse_square_tail N hN)
      (show 0 ≤ ‖s-1‖/(1/4 : ℝ) by positivity)
    apply this.trans
    rw [mul_one_div, div_le_iff₀ hN']
    linarith
  have hγ : ‖(Real.eulerMascheroniConstant : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_of_nonneg (by linarith [Real.one_half_lt_eulerMascheroniConstant])]
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hnorm := norm_sub_le ((∑ n ∈ Finset.range N, psiTerm n s) + ∑' k, psiTerm (k+N) s)
    (Real.eulerMascheroniConstant : ℂ)
  rw [hsplit, add_sub_cancel_right] at hnorm
  rw [← hsplit] at hnorm
  linarith [norm_add_le (∑ n ∈ Finset.range N, psiTerm n s) (∑' k, psiTerm (k+N) s),
    harmonic_le_one_add_log N, Real.log_le_log hN' hupper]

/-- Holomorphy of digamma at positive real part. -/
theorem analyticAt_digamma {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ digamma z := by
  have hg : AnalyticAt ℂ Complex.Gamma z := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hz] with w hw
    exact Complex.differentiableAt_Gamma w fun n h ↦ by simp [h] at hw; linarith
  exact hg.deriv.div hg (Gamma_ne_zero_of_re_pos hz)

end WeilExplicit
