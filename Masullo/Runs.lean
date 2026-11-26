import Masullo.Dyadic
import WeilExplicit.ExplicitFormula
import WeilExplicit.Controls
import WeilExplicit.Density

/-!
# Fixed-ratio sign runs and one-sided bounds of the dyadic sum

Let `dyadicDiff x ≥ -C x ^ θ` on `[Y, RY]`, or `dyadicDiff x ≤ C x ^ θ` on `[Y, RY]`, for a
fixed `R > 1` and arbitrarily large `Y`. Then some zero has maximal real part, or every zero in
the critical strip has real part at most `max θ (1/2)` (`exists_rightmost_of_bound`). The input
on the zeros is that those to the right of each line `re s = σ > 1/2` have summable reciprocal
ordinates (`WeilExplicit.summable_inv_im_of_half_lt`). For `θ < 1` the bound gives the trace
identity for all tests at a positive width below `1/2` (`trace_width_of_bound`). Sign runs are
the case `C = 0`. On windows `[Y, Y ^ (1 + δ)]` the same argument gives the exact exponent: for
`θ ≥ 1/2`, a bound `ε dyadicDiff x ≥ -C x ^ θ` with a sign `ε = ±1` that may depend on `Y` rules
out zeros to the right of `θ` (`ne_zero_of_dyadic_window`).

The proof feeds Weil's explicit formula a smoothed version of the kernel of `dyadicDiff` in
the logarithmic variable, then averages over the shifts of products of two-point probability
measures. Each measure cancels one zero and its conjugate. One zero `ρ₀` of least ordinate to
the right of a cutoff `σ` survives, by an odd-ratio argument. If the supremum of the real parts
is not attained, the cutoff can approach it while the total shift tends to zero. With the
cutoff at least `θ`, `dyadicDiff` then exceeds `C x ^ θ` and falls below `-C x ^ θ` in every late
window `[Y, RY]` (`both_signs`).

The averages are taken over finite sub-products and passed to the limit by dominated
convergence of the zero sum. The archimedean term is bounded by a multiple of `e^{t/2}` without
oscillation estimates.

OpenAI Codex proposed the fixed-ratio sign-run argument for the dyadic prime sum and the
positive two-point averages that isolate a conjugate pair. A Claude Fable subagent proposed
the one-sided power-bound form. Claude formalised both in Lean.
-/

open MeasureTheory Complex Set Filter Topology
open ArithmeticFunction (vonMangoldt_nonneg)
open scoped ArithmeticFunction.vonMangoldt Real

namespace Masullo.Runs

open Window WeilExplicit
open WeilExplicit (transform)

/-! ### The kernel of `dyadicDiff` in the logarithmic variable -/

/-- `weight` in the logarithmic variable; it vanishes outside `(-log 4, 0)`. -/
noncomputable def logWeight (y : ℝ) : ℝ := weight (Real.exp y)

/-- The kernel of `dyadicDiff` in the logarithmic variable. -/
noncomputable def kern (y : ℝ) : ℝ := logWeight (y - Real.log 2) - 2 * logWeight y

/-- The Laplace transform `∫ e ^ (s y) f y dy`. -/
noncomputable def lap (f : ℝ → ℝ) (s : ℂ) : ℂ := ∫ y : ℝ, cexp (s * y) * f y

lemma exp_two_log : Real.exp (2 * Real.log 2) = 4 := by
  rw [show 2 * Real.log 2 = Real.log 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num, Real.exp_log (by norm_num)]

lemma logWeight_eq_zero {y : ℝ} (h : y ≤ -(2 * Real.log 2) ∨ 0 ≤ y) : logWeight y = 0 := by
  refine le_antisymm (not_lt.1 fun hp => ?_) (weight_nonneg _)
  obtain ⟨h1, h2⟩ := (weight_pos_iff (Real.exp_pos y)).1 hp
  rcases h with h | h
  · have := Real.exp_le_exp.2 h
    rw [Real.exp_neg, exp_two_log] at this
    linarith
  · linarith [Real.one_le_exp h]

lemma continuous_logWeight : Continuous logWeight := by
  have e : logWeight = fun y => max (min (Real.exp (-y) - 1) (2 - Real.exp (-y) / 2)) 0 := by
    funext y
    rw [logWeight, weight_eq, one_div, ← Real.exp_neg]
  rw [e]
  fun_prop

lemma logWeight_of_mem {y : ℝ} (h1 : -Real.log 2 ≤ y) (h2 : y ≤ 0) :
    logWeight y = Real.exp (-y) - 1 := by
  have a := Real.exp_le_exp.2 (neg_le.2 h1)
  have b := Real.exp_le_exp.2 (neg_nonneg.2 h2)
  rw [Real.exp_log two_pos, Real.exp_zero] at *
  rw [logWeight, weight_eq, one_div, ← Real.exp_neg, min_eq_left (by linarith),
    max_eq_left (by linarith)]

lemma logWeight_of_mem' {y : ℝ} (h1 : -(2 * Real.log 2) ≤ y) (h2 : y ≤ -Real.log 2) :
    logWeight y = 2 - Real.exp (-y) / 2 := by
  have a := Real.exp_le_exp.2 (neg_le.2 h1)
  have b := Real.exp_le_exp.2 (le_neg.2 h2)
  rw [exp_two_log] at a
  rw [Real.exp_log two_pos] at b
  rw [logWeight, weight_eq, one_div, ← Real.exp_neg, min_eq_right (by linarith),
    max_eq_left (by linarith)]

lemma kern_eq_zero {y : ℝ} (h : y ≤ -(2 * Real.log 2) ∨ Real.log 2 ≤ y) : kern y = 0 := by
  have hL := Real.log_pos one_lt_two
  rw [kern, logWeight_eq_zero (by rcases h with h | h <;> [left; right] <;> linarith),
    logWeight_eq_zero (by rcases h with h | h <;> [left; right] <;> linarith)]
  ring

lemma continuous_kern : Continuous kern := by
  unfold kern
  have := continuous_logWeight
  fun_prop

lemma hasCompactSupport_of_eq_zero {M : Type*} [Zero M] {f : ℝ → M} {a b : ℝ}
    (h : ∀ y, y ≤ a ∨ b ≤ y → f y = 0) :
    HasCompactSupport f :=
  HasCompactSupport.intro isCompact_Icc fun y hy => h y (by
    simp only [mem_Icc, not_and_or, not_le] at hy
    rcases hy with hy | hy <;> [left; right] <;> linarith)

lemma integrable_lap {f : ℝ → ℝ} (hc : Continuous f) (hf : HasCompactSupport f) (s : ℂ) :
    Integrable fun y : ℝ => cexp (s * y) * f y :=
  (by fun_prop : Continuous fun y : ℝ => cexp (s * y) * f y).integrable_of_hasCompactSupport
    (hf.comp_left ofReal_zero).mul_left

lemma lap_kern (s : ℂ) : lap kern s = (cexp (s * Real.log 2) - 2) * lap logWeight s := by
  have hc := hasCompactSupport_of_eq_zero (f := logWeight) fun y h =>
    logWeight_eq_zero (by rcases h with h | h <;> [left; right] <;> exact h)
  have i1 := integrable_lap continuous_logWeight hc s
  have i2 : Integrable fun y : ℝ => cexp (s * y) * logWeight (y - Real.log 2) := by
    have := (i1.comp_sub_right (Real.log 2)).const_mul (cexp (s * Real.log 2))
    refine this.congr (.of_forall fun y => ?_)
    simp only [ofReal_sub, ← mul_assoc, ← Complex.exp_add]
    ring_nf
  have e : ∫ y : ℝ, cexp (s * y) * logWeight (y - Real.log 2) =
      cexp (s * Real.log 2) * lap logWeight s := by
    rw [← integral_add_right_eq_self _ (Real.log 2), lap, ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [ofReal_add, add_sub_cancel_right, ← mul_assoc, ← Complex.exp_add]
    ring_nf
  simp only [lap, kern, ofReal_sub, ofReal_mul, ofReal_ofNat, mul_sub, mul_left_comm _ (2 : ℂ)]
  rw [integral_sub i2 (i1.const_mul 2), e, integral_const_mul, lap]
  ring

lemma cexp_log_two : cexp (Real.log 2) = 2 := by
  rw [← ofReal_exp, Real.exp_log two_pos]; norm_num

lemma lap_logWeight {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : s * (s - 1) * lap logWeight s =
    (1 - cexp (-(s * Real.log 2))) * (1 - 2 * cexp (-(s * Real.log 2))) := by
  set L := Real.log 2
  have hL : 0 < L := Real.log_pos one_lt_two
  let f (u : ℝ) := cexp (s * u) * logWeight u
  have cf : Continuous f := by have := continuous_logWeight; fun_prop
  have hf : lap logWeight s = ∫ u in -(2 * L)..0, f u := by
    rw [intervalIntegral.integral_of_le (by linarith),
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · rfl
    · intro u hu
      have hz : logWeight u = 0 := logWeight_eq_zero (by
        simp only [mem_Ioc, not_and_or, not_lt, not_le] at hu
        exact hu.imp_right le_of_lt)
      simp [f, hz]
  set x := cexp (-(s * L)) with hx
  have hh (u : ℝ) (hu : u ∈ uIcc (-L) 0) : f (u - L) + f u =
      (2*x-1) * cexp (s * u) + (1-x) * cexp ((s-1) * u) := by
    rw [uIcc_of_le (by linarith)] at hu
    have ha : -(2 * L) ≤ u - L := by linarith [hu.1]
    have hb : u - L ≤ -L := by linarith [hu.2]
    simp only [f, logWeight_of_mem' ha hb, logWeight_of_mem hu.1 hu.2, neg_sub,
      Real.exp_sub, show Real.exp L = 2 from Real.exp_log two_pos]
    push_cast
    simp only [mul_sub, Complex.exp_sub, x, Complex.exp_neg, sub_mul, one_mul]
    field_simp
    ring
  have ci (c : ℂ) : Continuous (fun u : ℝ => cexp (c * u)) := by fun_prop
  have hc : Continuous (fun u : ℝ => f (u - L)) := cf.comp (continuous_id.sub continuous_const)
  rw [hf, ← intervalIntegral.integral_add_adjacent_intervals (b := -L) (cf.intervalIntegrable _ _)
    (cf.intervalIntegrable _ _), show -(2*L) = -L - L by ring, ← zero_sub L,
    ← intervalIntegral.integral_comp_sub_right f L, ← intervalIntegral.integral_add
      (hc.intervalIntegrable _ _) (cf.intervalIntegrable _ _),
    zero_sub L, intervalIntegral.integral_congr hh, intervalIntegral.integral_add
      (((ci s).intervalIntegrable _ _).const_mul (2*x-1))
      (((ci (s-1)).intervalIntegrable _ _).const_mul (1-x)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_exp_mul_complex h0, integral_exp_mul_complex (sub_ne_zero.2 h1)]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, ofReal_neg, mul_neg, ← hx]
  have h1x : cexp (-((s - 1) * L)) = 2 * x := by
    rw [hx, ← cexp_log_two, ← Complex.exp_add]; ring_nf; rfl
  rw [h1x]
  field_simp
  ring

/-- The transform of the kernel has no zeros in the open critical strip. -/
lemma lap_kern_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) : lap kern s ≠ 0 := by
  obtain ⟨hl, hu⟩ := Landau.Continues.exp_bounds h0 h1
  have h₁ : Landau.Continues.factor 1 s ≠ 0 :=
    Landau.Continues.factor_ne_zero (by simpa using hl.ne)
  have h₂ : Landau.Continues.factor 2 s ≠ 0 :=
    Landau.Continues.factor_ne_zero (by simpa using hu.ne')
  have hW := lap_logWeight (s := s) (fun h => by simp [h] at h0) (fun h => by simp [h] at h1)
  have hW' : lap logWeight s ≠ 0 := fun h =>
    mul_ne_zero h₁ h₂ (by simpa [h, Landau.Continues.factor] using hW.symm)
  rw [lap_kern]
  refine mul_ne_zero (fun h => h₂ ?_) hW'
  rw [Landau.Continues.factor, Complex.exp_neg, sub_eq_zero.1 h]
  norm_num

lemma lap_kern_one : lap kern 1 = 0 := by
  rw [lap_kern, one_mul, cexp_log_two, sub_self, zero_mul]

lemma hasCompactSupport_kern : HasCompactSupport kern :=
  hasCompactSupport_of_eq_zero fun _ h => kern_eq_zero h

/-! ### Smoothing by a bump -/

section Bump

variable (b : ContDiffBump (0 : ℝ))

/-- The kernel smoothed by the normalised bump `b`. -/
noncomputable def smooth : ℝ → ℝ :=
  convolution (b.normed volume) kern (ContinuousLinearMap.lsmul ℝ ℝ) volume

lemma smooth_apply (x : ℝ) : smooth b x = ∫ u, b.normed volume u * kern (x - u) := rfl

lemma abs_lt_of_normed_ne_zero {u : ℝ} (h : b.normed volume u ≠ 0) : |u| < b.rOut := by
  have : u ∈ Function.support (b.normed volume) := h
  rw [b.support_normed_eq] at this
  simpa [Metric.mem_ball, Real.dist_eq] using this

lemma smooth_eq_zero {x : ℝ} (h : x ≤ -(2 * Real.log 2) - b.rOut ∨ Real.log 2 + b.rOut ≤ x) :
    smooth b x = 0 := by
  rw [smooth_apply]
  refine integral_eq_zero_of_ae (.of_forall fun u => ?_)
  by_cases hu : b.normed volume u = 0
  · simp [hu]
  · have := abs_lt_of_normed_ne_zero b hu
    rw [abs_lt] at this
    exact mul_eq_zero_of_right _
      (kern_eq_zero (y := x - u) (by rcases h with h | h <;> [left; right] <;> linarith))

lemma contDiff_smooth : ContDiff ℝ 2 (smooth b) :=
  b.hasCompactSupport_normed.contDiff_convolution_left (n := 2) _ b.contDiff_normed
    continuous_kern.locallyIntegrable

lemma hasCompactSupport_smooth : HasCompactSupport (smooth b) :=
  hasCompactSupport_of_eq_zero fun _ h => smooth_eq_zero b h

/-- The transform of a convolution is the product of the transforms. -/
lemma lap_smooth (s : ℂ) : lap (smooth b) s = lap (b.normed volume) s * lap kern s := by
  have hf := integrable_lap (b.continuous_normed (μ := volume)) b.hasCompactSupport_normed s
  have hg := integrable_lap continuous_kern hasCompactSupport_kern s
  have h := integral_convolution (L := ContinuousLinearMap.mul ℂ ℂ) (μ := volume) (ν := volume)
    hf hg
  have e (x : ℝ) : convolution (fun y : ℝ => cexp (s * y) * b.normed volume y)
      (fun y : ℝ => cexp (s * y) * kern y) (ContinuousLinearMap.mul ℂ ℂ) volume x =
      cexp (s * x) * smooth b x := by
    rw [convolution_def, smooth_apply, ← integral_complex_ofReal, ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun u => ?_)
    have : cexp (s * u) * cexp (s * ((x : ℂ) - u)) = cexp (s * x) := by
      rw [← Complex.exp_add]; ring_nf
    simp only [ContinuousLinearMap.mul_apply']
    push_cast
    linear_combination (b.normed volume u * kern (x - u) : ℂ) * this
  simp only [e, ContinuousLinearMap.mul_apply'] at h
  exact h

end Bump

/-- For every `s` some bump of arbitrarily small radius has a transform not vanishing at `s`. -/
lemma exists_bump (s : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ b : ContDiffBump (0 : ℝ), b.rOut ≤ r ∧ lap (b.normed volume) s ≠ 0 := by
  let g (y : ℝ) := cexp (-(s * y))
  have hg : Continuous g := by unfold g; fun_prop
  obtain ⟨δ, hδ, hd⟩ :=
    Metric.continuousAt_iff.1 (hg.continuousAt (x := 0)) (1 / 2) (by norm_num)
  let b : ContDiffBump (0 : ℝ) := ⟨min r δ / 2, min r δ, by positivity, by
    exact half_lt_self (lt_min hr hδ)⟩
  refine ⟨b, min_le_left _ _, fun hzero => ?_⟩
  have h := b.dist_normed_convolution_le (μ := volume) hg.aestronglyMeasurable
    (x₀ := 0) (ε := 1 / 2) fun y hy =>
      (hd ((Metric.mem_ball.1 hy).trans_le (min_le_right r δ))).le
  have he : convolution (b.normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume 0 =
      lap (b.normed volume) s := by
    simp [convolution_def, g, lap, Complex.real_smul, mul_comm]
  simp [he, hzero, g] at h
  linarith

/-! ### Weil's formula for the smoothed dyadic sum -/

section Formula

variable (b : ContDiffBump (0 : ℝ))

/-- The test of Weil's formula whose prime side is `smoothDiff b t`. -/
noncomputable def test (t u : ℝ) : ℂ := ((Real.exp (u / 2) * smooth b (u - t) : ℝ) : ℂ)

/-- `dyadicDiff` smoothed by `b` in the logarithmic variable, at `e ^ t`. -/
noncomputable def smoothDiff (t : ℝ) : ℝ := ∑' n : ℕ, Λ n * smooth b (Real.log n - t)

/-- The archimedean term of Weil's formula for `test b t`. -/
noncomputable def arch (t : ℝ) : ℂ := 1 / (2 * (π : ℂ)) * ∫ τ : ℝ, transform (test b t) τ *
    (((digamma (1 / 4 + I * τ / 2)).re - Real.log π : ℝ) : ℂ)

lemma contDiff_test (t : ℝ) : ContDiff ℝ 2 (test b t) :=
  ofRealCLM.contDiff.comp ((Real.contDiff_exp.comp (contDiff_id.div_const 2)).mul
    ((contDiff_smooth b).comp (contDiff_id.sub contDiff_const)))

lemma test_eq_zero (t : ℝ) {u : ℝ}
    (h : u ≤ t - 2 * Real.log 2 - b.rOut ∨ t + Real.log 2 + b.rOut ≤ u) : test b t u = 0 := by
  simp [test, smooth_eq_zero b (x := u - t) (by rcases h with h | h <;> [left; right] <;> linarith)]

lemma hasCompactSupport_test (t : ℝ) : HasCompactSupport (test b t) :=
  hasCompactSupport_of_eq_zero fun _ h => test_eq_zero b t h

lemma transform_test (t : ℝ) (z : ℂ) :
    transform (test b t) z = cexp ((1 / 2 + I * z) * t) * lap (smooth b) (1 / 2 + I * z) := by
  rw [WeilExplicit.transform, lap, ← integral_const_mul, ← integral_add_right_eq_self _ t]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [test, add_sub_cancel_right]
  push_cast
  have e : cexp ((y + t) / 2) * cexp (I * z * (y + t)) =
      cexp ((1 / 2 + I * z) * t) * cexp ((1 / 2 + I * z) * y) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
  linear_combination (smooth b y : ℂ) * e

lemma transform_test_zero (t : ℝ) (ρ : ℂ) :
    transform (test b t) ((ρ - 1 / 2) / I) = cexp (ρ * t) * lap (smooth b) ρ := by
  rw [transform_test, mul_div_cancel₀ _ I_ne_zero, add_sub_cancel]

/-- Weil's formula for `test b t`: the zero sum of the smoothed dyadic sum. -/
lemma hasSum_zeros {t : ℝ} (ht : 2 * Real.log 2 + b.rOut < t) :
    HasSum (fun ρ : stripZeros => (zeroMult ρ : ℂ) * (cexp (ρ * t) * lap (smooth b) ρ))
      (lap (smooth b) 0 - smoothDiff b t + arch b t) := by
  have h := explicit_formula (contDiff_test b t) (hasCompactSupport_test b t)
  have e2 : transform (test b t) (I / 2) = lap (smooth b) 0 := by
    rw [transform_test, ← mul_div_assoc, I_mul_I]; norm_num
  have e3 : transform (test b t) (-I / 2) = 0 := by
    rw [transform_test, mul_div_assoc', mul_neg, I_mul_I]
    norm_num [lap_smooth, lap_kern_one]
  have e4 : ∑' n : ℕ, ((Λ n / √n : ℝ) : ℂ) * (test b t (Real.log n) + test b t (-Real.log n)) =
      smoothDiff b t := by
    rw [smoothDiff, ofReal_tsum]
    congr 1 with n
    have hn := Real.log_natCast_nonneg n
    rw [test_eq_zero b t (u := -Real.log n) (by left; linarith), add_zero, test, ← ofReal_mul]
    congr 1
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    rw [Real.exp_half, Real.exp_log (by exact_mod_cast hn)]
    have : (0 : ℝ) < √n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    field_simp
  rw [e2, e3, e4, add_zero] at h
  simp only [transform_test_zero] at h
  exact h

lemma exists_arch_bound : ∃ C, ∀ t, ‖arch b t‖ ≤ C * Real.exp (t / 2) := by
  set g := fun τ : ℝ => ‖lap (smooth b) (1 / 2 + I * τ) *
    (((digamma (1 / 4 + I * τ / 2)).re - Real.log π : ℝ) : ℂ)‖
  refine ⟨1 / (2 * π) * ∫ τ, g τ, fun t => ?_⟩
  have e (τ : ℝ) : ‖transform (test b t) τ *
      (((digamma (1 / 4 + I * τ / 2)).re - Real.log π : ℝ) : ℂ)‖ = Real.exp (t / 2) * g τ := by
    rw [transform_test, mul_assoc, norm_mul, norm_exp]
    congr 2
    simp
    ring
  rw [arch, norm_mul]
  calc _ ≤ 1 / (2 * π) * ∫ τ : ℝ, ‖transform (test b t) τ *
        (((digamma (1 / 4 + I * τ / 2)).re - Real.log π : ℝ) : ℂ)‖ := by
        gcongr
        · norm_num [abs_of_pos Real.pi_pos]
        · exact norm_integral_le_integral_norm _
    _ = _ := by simp_rw [e]; rw [integral_const_mul]; ring

lemma summable_norm_lap :
    Summable fun ρ : stripZeros => (zeroMult ρ : ℝ) * ‖lap (smooth b) ρ‖ := by
  have h := summable_zero_transform (contDiff_test b 0) (hasCompactSupport_test b 0)
  simp only [transform_test_zero, ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h
  exact (summable_norm_iff.2 h).congr fun ρ => by rw [norm_mul, norm_natCast]

end Formula

/-! ### The smoothed sum as an average of `dyadicDiff` -/

lemma dyadicSum_eq_sum {X : ℝ} (hX : 0 < X) {N : ℕ} (hN : X < N) :
    dyadicSum X = ∑ n ∈ Finset.range N, Λ n * logWeight (Real.log n - Real.log X) := by
  have e (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊X⌋₊) :
      Λ n * weight (n / X) = Λ n * logWeight (Real.log n - Real.log X) := by
    have : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    rw [logWeight, Real.exp_sub, Real.exp_log this, Real.exp_log hX]
  rw [dyadicSum, Finset.sum_congr rfl e]
  refine Finset.sum_subset (fun n hn => ?_) (fun n _ hn' => ?_)
  · rw [Finset.mem_Icc, Nat.le_floor_iff hX.le] at hn
    exact Finset.mem_range.2 (by exact_mod_cast hn.2.trans_lt hN)
  · rcases Nat.eq_zero_or_pos n with rfl | h
    · simp
    have hXn : X < n := (Nat.floor_lt hX.le).1 (by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hn'; omega)
    rw [logWeight_eq_zero (Or.inr (sub_nonneg.2 (Real.log_le_log hX hXn.le))), mul_zero]

lemma dyadicDiff_eq_sum {X : ℝ} (hX : 0 < X) {N : ℕ} (hN : 2 * X < N) :
    dyadicDiff X = ∑ n ∈ Finset.range N, Λ n * kern (Real.log n - Real.log X) := by
  rw [dyadicDiff, dyadicSum_eq_sum (by positivity) hN, dyadicSum_eq_sum hX (by linarith),
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [kern, Real.log_mul two_ne_zero hX.ne']
  ring_nf

section Average

variable (b : ContDiffBump (0 : ℝ))

lemma smoothDiff_eq (t : ℝ) {N : ℕ} (hN : 2 * Real.exp (t + b.rOut) < N) :
    smoothDiff b t = ∫ u, b.normed volume u * dyadicDiff (Real.exp (t + u)) := by
  have hN0 : (0 : ℝ) < N := lt_trans (by positivity) hN
  rw [smoothDiff, tsum_eq_sum (s := Finset.range N) fun n hn => ?_]
  · simp_rw [smooth_apply, ← integral_const_mul]
    rw [← integral_finsetSum _ fun n _ => ?_]
    · refine integral_congr_ae (.of_forall fun u => ?_)
      by_cases hu : b.normed volume u = 0
      · simp [hu]
      have := abs_lt_of_normed_ne_zero b hu
      rw [abs_lt] at this
      simp only
      rw [dyadicDiff_eq_sum (Real.exp_pos _) (N := N) (lt_of_le_of_lt (by gcongr; linarith) hN),
        Real.log_exp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring_nf
    · exact (((b.continuous_normed (μ := volume)).mul (continuous_kern.comp
        (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
        b.hasCompactSupport_normed.mul_right).const_mul _
  · have hn : (N : ℝ) ≤ n := by exact_mod_cast not_lt.1 (Finset.mem_range.not.1 hn)
    have := Real.log_lt_log (by positivity) (hN.trans_le hn)
    rw [Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp] at this
    rw [smooth_eq_zero b (Or.inr (by linarith)), mul_zero]

/-- A lower bound `-B ≤ ε dyadicDiff` with `0 ≤ B` on `[e ^ (t - r), e ^ (t + r)]` passes to
`ε smoothDiff b t`, where `r` is the radius of `b`. -/
lemma smoothDiff_sign {t ε B : ℝ} (hB : 0 ≤ B)
    (h : ∀ x ∈ Icc (Real.exp (t - b.rOut)) (Real.exp (t + b.rOut)), -B ≤ ε * dyadicDiff x) :
    -B ≤ ε * smoothDiff b t := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * Real.exp (t + b.rOut))
  rw [smoothDiff_eq b t hN]
  by_cases hi : Integrable fun u => b.normed volume u * dyadicDiff (Real.exp (t + u))
  swap
  · rw [integral_undef hi, mul_zero]; linarith
  calc -B = ∫ u, b.normed volume u * -B := by rw [integral_mul_const, b.integral_normed, one_mul]
    _ ≤ _ := by
      rw [← integral_const_mul]
      refine integral_mono (b.integrable_normed.mul_const _) (hi.const_mul ε) fun u => ?_
      by_cases hu : b.normed volume u = 0
      · simp [hu]
      have := abs_lt_of_normed_ne_zero b hu
      rw [abs_lt] at this
      have := mul_le_mul_of_nonneg_left (h (Real.exp (t + u)) ⟨Real.exp_le_exp.2 (by linarith),
        Real.exp_le_exp.2 (by linarith)⟩) (b.nonneg_normed (μ := volume) u)
      dsimp only
      linarith

end Average

/-! ### Averages over two-point measures -/

/-- The transform of the probability measure with mass `q` at `d` and `1 - q` at `0`. -/
noncomputable def factor (q d : ℝ) (s : ℂ) : ℂ := 1 + q * (cexp (s * d) - 1)

lemma factor_conj (q d : ℝ) (s : ℂ) :
    factor q d (starRingEnd ℂ s) = starRingEnd ℂ (factor q d s) := by
  simp [factor, ← Complex.exp_conj]

lemma norm_factor_le {q d : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hd : 0 ≤ d) {s : ℂ} (hs : s.re ≤ 1) :
    ‖factor q d s‖ ≤ Real.exp d := by
  have e : factor q d s = (1 - q : ℝ) + q * cexp (s * d) := by push_cast [factor]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_real, norm_mul, norm_real, norm_exp, re_mul_ofReal, Real.norm_of_nonneg (by linarith),
    Real.norm_of_nonneg hq0]
  have h1 : 1 ≤ Real.exp d := Real.one_le_exp hd
  have h2 : Real.exp (s.re * d) ≤ Real.exp d := Real.exp_le_exp.2 (by nlinarith)
  nlinarith

lemma norm_factor_sub_one_le {q d : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {s : ℂ}
    (h : ‖s‖ * |d| ≤ 1) : ‖factor q d s - 1‖ ≤ 2 * ‖s‖ * |d| := by
  rw [factor, add_sub_cancel_left, norm_mul, norm_real, Real.norm_of_nonneg hq0]
  have h1 : ‖s * d‖ = ‖s‖ * |d| := by rw [norm_mul, norm_real, Real.norm_eq_abs]
  have := norm_exp_sub_one_le (x := s * d) (h1 ▸ h)
  rw [h1] at this
  nlinarith [norm_nonneg (cexp (s * d) - 1)]

lemma sum_weights {J : Type*} [DecidableEq J] (q : J → ℝ) (F : Finset J) :
    ∑ S ∈ F.powerset, (∏ j ∈ S, q j) * ∏ j ∈ F \ S, (1 - q j) = 1 := by
  rw [← Finset.prod_add]
  simp

/-- A finite product of factors as an average of exponentials. -/
lemma prod_factor {J : Type*} [DecidableEq J] (q d : J → ℝ) (F : Finset J) (s : ℂ) (t : ℝ) :
    cexp (s * t) * ∏ j ∈ F, factor (q j) (d j) s = ∑ S ∈ F.powerset,
      (((∏ j ∈ S, q j) * ∏ j ∈ F \ S, (1 - q j) : ℝ) : ℂ) * cexp (s * (t + ∑ j ∈ S, d j)) := by
  have e (j : J) : factor (q j) (d j) s = q j * cexp (s * d j) + (1 - q j : ℝ) := by
    push_cast [factor]; ring
  simp_rw [e, Finset.prod_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_mul_distrib]
  push_cast
  rw [mul_add, Finset.mul_sum, Complex.exp_add, Complex.exp_sum]
  ring

section Limit

variable (b : ContDiffBump (0 : ℝ)) {J : Type*} (q d : J → ℝ)

/-- If `-B ≤ ε smoothDiff b` on `[t, t + L]`, the zero sum of Weil's formula weighted
by a finite product of two-point factors is bounded by `B` and the pole and archimedean terms. -/
lemma avg_bound [DecidableEq J] (hq : ∀ j, 0 ≤ q j ∧ q j ≤ 1) (hd : ∀ j, 0 ≤ d j)
    (F : Finset J) {L C ε t B : ℝ} (hL : ∑ j ∈ F, d j ≤ L)
    (hC : ∀ t, ‖arch b t‖ ≤ C * Real.exp (t / 2))
    (hε : |ε| = 1) (ht : 2 * Real.log 2 + b.rOut < t)
    (hs : ∀ u ∈ Icc 0 L, -B ≤ ε * smoothDiff b (t + u)) :
    ε * (∑' ρ : stripZeros, (zeroMult ρ : ℂ) * (cexp (ρ * t) * lap (smooth b) ρ) *
      ∏ j ∈ F, factor (q j) (d j) ρ).re ≤
      ‖lap (smooth b) 0‖ + C * Real.exp ((t + L) / 2) + B := by
  set w : Finset J → ℝ := fun S => (∏ j ∈ S, q j) * ∏ j ∈ F \ S, (1 - q j)
  have hw (S : Finset J) : 0 ≤ w S := mul_nonneg (Finset.prod_nonneg fun j _ => (hq j).1)
    (Finset.prod_nonneg fun j _ => by linarith [(hq j).2])
  have hu (S : Finset J) (hS : S ∈ F.powerset) : ∑ j ∈ S, d j ∈ Icc 0 L :=
    ⟨Finset.sum_nonneg fun j _ => hd j, (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.mem_powerset.1 hS) fun j _ _ => hd j).trans hL⟩
  have hsum := hasSum_sum fun S (hS : S ∈ F.powerset) =>
    (hasSum_zeros b (t := t + ∑ j ∈ S, d j) (by linarith [(hu S hS).1])).mul_left (w S : ℂ)
  have e : (fun ρ : stripZeros => ∑ S ∈ F.powerset, (w S : ℂ) * ((zeroMult ρ : ℂ) *
      (cexp (ρ * ↑(t + ∑ j ∈ S, d j)) * lap (smooth b) ρ))) =
      fun ρ : stripZeros => (zeroMult ρ : ℂ) *
      (cexp (ρ * t) * lap (smooth b) ρ) * ∏ j ∈ F, factor (q j) (d j) ρ := by
    funext ρ
    rw [mul_comm (cexp _), mul_assoc, mul_assoc, prod_factor, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [w]
    push_cast
    ring
  rw [e] at hsum
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0)
    rwa [zero_div, Real.exp_zero, mul_one] at this
  rw [hsum.tsum_eq, re_sum, Finset.mul_sum]
  calc _ ≤ ∑ S ∈ F.powerset, w S * (‖lap (smooth b) 0‖ + C * Real.exp ((t + L) / 2) + B) := by
        refine Finset.sum_le_sum fun S hS => ?_
        rw [re_ofReal_mul, mul_left_comm]
        refine mul_le_mul_of_nonneg_left ?_ (hw S)
        have h1 := hs _ (hu S hS)
        have h2 := hC (t + ∑ j ∈ S, d j)
        have h3 : Real.exp ((t + ∑ j ∈ S, d j) / 2) ≤ Real.exp ((t + L) / 2) :=
          Real.exp_le_exp.2 (by linarith [(hu S hS).2])
        have k (z : ℂ) : ε * z.re ≤ ‖z‖ := by
          calc ε * z.re ≤ |ε * z.re| := le_abs_self _
            _ ≤ ‖z‖ := by rw [abs_mul, hε, one_mul]; exact abs_re_le_norm z
        simp only [add_re, sub_re, ofReal_re, mul_add, mul_sub]
        linarith [k (lap (smooth b) 0), k (arch b (t + ∑ j ∈ S, d j)),
          mul_le_mul_of_nonneg_left h3 hC0]
    _ = _ := by rw [← Finset.sum_mul, sum_weights, one_mul]

/-- The bound of `avg_bound` for an infinite product of two-point factors. -/
lemma limit_bound (hq : ∀ j, 0 ≤ q j ∧ q j ≤ 1) (hd : ∀ j, 0 ≤ d j) {M : ℂ → ℂ}
    (hM : ∀ ρ : stripZeros, HasProd (fun j => factor (q j) (d j) ρ) (M ρ))
    {L C ε t B : ℝ} (hL : ∀ F : Finset J, ∑ j ∈ F, d j ≤ L)
    (hC : ∀ t, ‖arch b t‖ ≤ C * Real.exp (t / 2))
    (hε : |ε| = 1) (ht : 2 * Real.log 2 + b.rOut < t)
    (hs : ∀ u ∈ Icc 0 L, -B ≤ ε * smoothDiff b (t + u)) :
    ε * (∑' ρ : stripZeros, (zeroMult ρ : ℂ) * (cexp (ρ * t) * lap (smooth b) ρ) * M ρ).re ≤
      ‖lap (smooth b) 0‖ + C * Real.exp ((t + L) / 2) + B := by
  classical
  have ht0 : 0 ≤ t := by linarith [Real.log_pos one_lt_two, b.rOut_pos]
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (F : Finset J) (ρ : stripZeros) => (zeroMult ρ : ℂ) * (cexp (ρ * t) *
      lap (smooth b) ρ) * ∏ j ∈ F, factor (q j) (d j) ρ)
    (bound := fun ρ => Real.exp t * Real.exp L * ((zeroMult ρ : ℝ) * ‖lap (smooth b) ρ‖))
    ((summable_norm_lap b).mul_left _) (fun ρ => by
      have := hM ρ
      rw [HasProd, SummationFilter.unconditional_filter] at this
      exact this.const_mul _) (.of_forall fun F ρ => ?_)
  · refine le_of_tendsto' ((continuous_const.mul continuous_re).tendsto _ |>.comp hlim)
      fun F => avg_bound b q d hq hd F (hL F) hC hε ht hs
  · have h1 : ‖cexp (ρ * t)‖ ≤ Real.exp t := by
      rw [norm_exp, re_mul_ofReal]
      exact Real.exp_le_exp.2 (by nlinarith [ρ.2.2.2])
    have h2 : ‖∏ j ∈ F, factor (q j) (d j) ρ‖ ≤ Real.exp L := by
      refine (Finset.norm_prod_le _ _).trans ?_
      refine (Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ =>
        norm_factor_le (hq j).1 (hq j).2 (hd j) ρ.2.2.2.le).trans ?_
      rw [← Real.exp_sum]
      exact Real.exp_le_exp.2 (hL F)
    rw [norm_mul, norm_mul, norm_mul, norm_natCast]
    have := norm_nonneg (lap (smooth b) ρ)
    have := norm_nonneg (cexp (ρ * t))
    have : (0 : ℝ) ≤ zeroMult ρ := Nat.cast_nonneg _
    calc _ ≤ (zeroMult ρ : ℝ) * (Real.exp t * ‖lap (smooth b) ρ‖) * Real.exp L := by gcongr
      _ = _ := by ring

end Limit

/-! ### Isolation of one conjugate pair -/

lemma lap_conj (f : ℝ → ℝ) (s : ℂ) : lap f (starRingEnd ℂ s) = starRingEnd ℂ (lap f s) := by
  rw [lap, lap, ← integral_conj]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp [← Complex.exp_conj]

lemma cexp_mul_real (s : ℂ) (d : ℝ) :
    cexp (s * d) = Real.exp (s.re * d) * cexp ((s.im * d : ℝ) * I) := by
  rw [ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp

/-- The shift of the two-point measure attached to a zero. -/
noncomputable def shift (ρ : ℂ) : ℝ := π / ρ.im

/-- The mass at the shift of the two-point measure attached to a zero. -/
noncomputable def mass (ρ : ℂ) : ℝ := 1 / (1 + Real.exp (ρ.re * shift ρ))

lemma mass_mem (ρ : ℂ) : 0 ≤ mass ρ ∧ mass ρ ≤ 1 := by
  have := Real.exp_pos (ρ.re * shift ρ)
  exact ⟨by unfold mass; positivity, by rw [mass, div_le_one (by positivity)]; linarith⟩

lemma factor_eq_zero_iff {ρ s : ℂ} :
    factor (mass ρ) (shift ρ) s = 0 ↔ cexp (s * shift ρ) = -Real.exp (ρ.re * shift ρ) := by
  have h : (1 + Real.exp (ρ.re * shift ρ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < 1 + Real.exp (ρ.re * shift ρ)).ne'
  have e : factor (mass ρ) (shift ρ) s =
      (Real.exp (ρ.re * shift ρ) + cexp (s * shift ρ)) / (1 + Real.exp (ρ.re * shift ρ)) := by
    rw [factor, mass, ofReal_div, ofReal_one, ofReal_add, ofReal_one]
    generalize (Real.exp (ρ.re * shift ρ) : ℂ) = E at h ⊢
    field_simp
    ring
  rw [e, div_eq_zero_iff, or_iff_left h]
  constructor <;> intro h' <;> linear_combination h'

/-- The factor attached to a zero vanishes at that zero and at its conjugate. -/
lemma factor_self {ρ : ℂ} (hρ : 0 < ρ.im) :
    factor (mass ρ) (shift ρ) ρ = 0 ∧ factor (mass ρ) (shift ρ) (starRingEnd ℂ ρ) = 0 := by
  have e : ρ.im * shift ρ = π := by rw [shift]; field_simp
  refine ⟨factor_eq_zero_iff.2 ?_, factor_eq_zero_iff.2 ?_⟩ <;> rw [cexp_mul_real]
  · rw [e, exp_pi_mul_I]; ring
  · rw [conj_re, conj_im, neg_mul, e, ofReal_neg, neg_mul, Complex.exp_neg, exp_pi_mul_I]; ring

/-- The factor attached to a zero of ordinate at least that of `ρ₀` keeps `ρ₀`, unless the
zero is `ρ₀` itself: a vanishing factor forces equal real parts and an odd ordinate ratio. -/
lemma factor_ne_zero {ρ ρ₀ : ℂ} (h0 : 0 < ρ₀.im) (hle : ρ₀.im ≤ ρ.im) (hne : ρ ≠ ρ₀) :
    factor (mass ρ) (shift ρ) ρ₀ ≠ 0 := by
  intro h
  have hρ := h0.trans_le hle
  have hd : 0 < shift ρ := div_pos Real.pi_pos hρ
  have hi : (ρ * shift ρ).im = π := by rw [im_mul_ofReal, shift]; field_simp
  have hi₀ : (ρ₀ * shift ρ).im ≤ π := hi ▸ (by simpa using mul_le_mul_of_nonneg_right hle hd.le)
  have e := (factor_eq_zero_iff.1 (factor_self hρ).1).trans (factor_eq_zero_iff.1 h).symm
  apply hne
  apply mul_right_cancel₀ (b := (shift ρ : ℂ)) (ofReal_ne_zero.mpr hd.ne')
  apply exp_inj_of_neg_pi_lt_of_le_pi _ hi.le _ hi₀ e
  · rw [hi]; linarith [Real.pi_pos]
  · rw [im_mul_ofReal]; linarith [mul_pos h0 hd, Real.pi_pos]

section Product

variable {J : Set ℂ} (hJ : ∀ j ∈ J, 0 < j.im) (hs : Summable fun j : J => shift j)
include hJ hs

lemma summable_factor_sub_one (s : ℂ) :
    Summable fun j : J => ‖factor (mass j) (shift j) s - 1‖ := by
  refine Summable.of_norm_bounded_eventually (hs.mul_left (2 * ‖s‖)) ?_
  have := hs.tendsto_cofinite_zero (Iic_mem_nhds (by positivity : (0 : ℝ) < 1 / (‖s‖ + 1)))
  filter_upwards [this] with j hj
  have h0 : 0 ≤ shift j := (div_pos Real.pi_pos (hJ j j.2)).le
  have hj : shift j ≤ 1 / (‖s‖ + 1) := hj
  rw [norm_norm]
  refine (norm_factor_sub_one_le (mass_mem _).1 (mass_mem _).2 ?_).trans_eq
    (by rw [abs_of_nonneg h0, mul_assoc])
  rw [abs_of_nonneg h0]
  calc ‖s‖ * shift j ≤ ‖s‖ * (1 / (‖s‖ + 1)) := by gcongr
    _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith

lemma multipliable_factor (s : ℂ) : Multipliable fun j : J => factor (mass j) (shift j) s := by
  simpa using multipliable_one_add_of_summable (summable_factor_sub_one hJ hs s)

lemma tprod_factor_ne_zero {s : ℂ} (h : ∀ j : J, factor (mass j) (shift j) s ≠ 0) :
    ∏' j : J, factor (mass j) (shift j) s ≠ 0 := by
  simpa using tprod_one_add_ne_zero_of_summable (by simpa using h)
    (summable_factor_sub_one hJ hs s)

lemma tprod_factor_conj (s : ℂ) : ∏' j : J, factor (mass j) (shift j) (starRingEnd ℂ s) =
    starRingEnd ℂ (∏' j : J, factor (mass j) (shift j) s) := by
  simp_rw [factor_conj]
  exact ((multipliable_factor hJ hs s).map_tprod (starRingEnd ℂ) continuous_conj).symm

end Product

lemma exp_dominates {a c β σ t : ℝ} (ha : 0 < a) (hσ : σ < β)
    (ht : c / (a * (β - σ)) < t) : c * Real.exp (σ * t) < a * Real.exp (β * t) := by
  have h1 : c < a * ((β - σ) * t) := by
    rw [div_lt_iff₀ (by nlinarith)] at ht; linarith
  have h2 := Real.add_one_le_exp ((β - σ) * t)
  have h3 : Real.exp (β * t) = Real.exp (σ * t) * Real.exp ((β - σ) * t) := by
    rw [← Real.exp_add]; ring_nf
  have h4 := Real.exp_pos (σ * t)
  have h5 : c < a * Real.exp ((β - σ) * t) := by nlinarith
  rw [h3]
  nlinarith [mul_lt_mul_of_pos_left h5 h4]

lemma norm_term_le (b : ContDiffBump (0 : ℝ)) {t κ L : ℝ} {N : ℂ} (hN : ‖N‖ ≤ Real.exp L)
    (ρ : stripZeros) (hρ : (ρ : ℂ).re * t ≤ κ) :
    ‖(zeroMult ρ : ℂ) * (cexp (ρ * t) * lap (smooth b) ρ) * N‖ ≤
      Real.exp κ * Real.exp L * ((zeroMult ρ : ℝ) * ‖lap (smooth b) ρ‖) := by
  rw [norm_mul, norm_mul, norm_mul, norm_natCast, norm_exp, re_mul_ofReal]
  have := norm_nonneg (lap (smooth b) ρ)
  have : (0 : ℝ) ≤ zeroMult ρ := Nat.cast_nonneg _
  have := Real.exp_le_exp.2 hρ
  calc _ ≤ (zeroMult ρ : ℝ) * (Real.exp κ * ‖lap (smooth b) ρ‖) * Real.exp L := by gcongr
    _ = _ := by ring

/-! ### Both signs in every long window -/

lemma conj_mem_stripZeros {ρ : ℂ} (h : ρ ∈ stripZeros) : starRingEnd ℂ ρ ∈ stripZeros :=
  ⟨by rw [riemannZeta_conj, h.1, map_zero], by simpa using h.2.1, by simpa using h.2.2⟩

lemma im_ne_zero_of_mem {ρ : ℂ} (h : ρ ∈ stripZeros) : ρ.im ≠ 0 := by
  intro h0
  have e : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [h0])
  exact riemannZeta_ofReal_ne_zero h.2.1 h.2.2 (e ▸ h.1)

/-- Zeros of positive ordinate strictly to the right of `σ`. -/
def upper (σ : ℝ) : Set ℂ := {ρ | ρ ∈ stripZeros ∧ σ < ρ.re ∧ 0 < ρ.im}

/-- A zero in the strip to the right of `σ` yields one of positive ordinate, by conjugation. -/
lemma upper_nonempty {σ : ℝ} {ρ : ℂ} (hρ : ρ ∈ stripZeros) (hl : σ < ρ.re) :
    (upper σ).Nonempty := by
  rcases lt_or_gt_of_ne (im_ne_zero_of_mem hρ) with hi | hi
  · exact ⟨starRingEnd ℂ ρ, conj_mem_stripZeros hρ, by simpa using hl, by simpa using hi⟩
  · exact ⟨ρ, hρ, hl, hi⟩

/-- A nonempty `upper σ` with summable reciprocal ordinates has an element of least ordinate. -/
lemma exists_min_im {σ : ℝ} (hne : (upper σ).Nonempty)
    (hsum : Summable fun z : upper σ => 1 / (z : ℂ).im) :
    ∃ ρ₀ ∈ upper σ, ∀ ρ ∈ upper σ, ρ₀.im ≤ ρ.im := by
  have hpos : Tendsto (fun z : upper σ => 1 / (z : ℂ).im) cofinite (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hsum.tendsto_cofinite_zero,
      .of_forall fun z => one_div_pos.2 z.2.2.2⟩
  have him : Tendsto (fun z : upper σ => (z : ℂ).im) cofinite atTop := by
    simpa [Function.comp_def, one_div] using tendsto_inv_nhdsGT_zero.comp hpos
  let : Nonempty (upper σ) := hne.to_subtype
  obtain ⟨ρ₀, hmin⟩ := him.exists_forall_le
  exact ⟨ρ₀, ρ₀.2, fun ρ hρ => hmin ⟨ρ, hρ⟩⟩

/-- Let `ρ₀` have least ordinate among the zeros of positive ordinate to the right of
`σ ≥ 1/2`, and let the reciprocal ordinates of these zeros have sum `S` with `3πS < log R`.
Let `0 ≤ C` and `0 ≤ θ ≤ σ`. Then from some height on, every window `[Y, RY]` contains points
where `dyadicDiff x < -C x ^ θ` and points where `dyadicDiff x > C x ^ θ`. -/
theorem both_signs {σ R θ C : ℝ} (hσ : 1 / 2 ≤ σ) (hR : 0 < R) (hθ : 0 ≤ θ) (hθσ : θ ≤ σ)
    (hC : 0 ≤ C) {ρ₀ : ℂ} (h₀ : ρ₀ ∈ upper σ)
    (hmin : ∀ ρ ∈ upper σ, ρ₀.im ≤ ρ.im)
    (hsum : Summable fun ρ : upper σ => 1 / (ρ : ℂ).im)
    (hW : 3 * π * ∑' ρ : upper σ, 1 / (ρ : ℂ).im < Real.log R) :
    ∃ Y₀, ∀ Y ≥ Y₀, ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      ¬ ∀ x ∈ Icc Y (R * Y), -(C * x ^ θ) ≤ ε * dyadicDiff x := by
  classical
  obtain ⟨hz₀, hσ₀, hγ₀⟩ := h₀
  set S := ∑' ρ : upper σ, 1 / (ρ : ℂ).im
  have hpos (ρ : upper σ) : 0 < 1 / (ρ : ℂ).im := one_div_pos.2 ρ.2.2.2
  have hS0 : 1 / ρ₀.im ≤ S := hsum.le_tsum ⟨ρ₀, hz₀, hσ₀, hγ₀⟩ fun j _ => (hpos j).le
  have hS : 0 ≤ S := (one_div_pos.2 hγ₀).le.trans hS0
  -- the smoothing bump
  set r := (Real.log R - 3 * π * S) / 2
  obtain ⟨b, hbr, hb⟩ := exists_bump ρ₀ (r := r) (by simp only [r]; linarith)
  have hb0 := b.rOut_pos
  set K := lap (smooth b)
  have hK : K ρ₀ ≠ 0 := by
    simp only [K]; rw [lap_smooth]; exact mul_ne_zero hb (lap_kern_ne_zero hz₀.2.1 hz₀.2.2)
  -- the isolating product
  set J : Set ℂ := {ρ | ρ ∈ upper σ ∧ ρ ≠ ρ₀}
  have hJsub : J ⊆ upper σ := fun ρ h => h.1
  have hJ : ∀ j ∈ J, 0 < j.im := fun j h => h.1.2.2
  have hshift : Summable fun j : J => shift j := by
    refine ((hsum.comp_injective (Set.inclusion_injective hJsub)).mul_left π).congr fun j => ?_
    simp [shift, div_eq_mul_inv]
  set L := π * S
  have hL (F : Finset J) : ∑ j ∈ F, shift j ≤ L := by
    have e : ∑ j ∈ F, shift j =
        π * ∑ j ∈ F.map ⟨_, Set.inclusion_injective hJsub⟩, 1 / (j : ℂ).im := by
      rw [Finset.sum_map, Finset.mul_sum]; simp [shift, div_eq_mul_inv]
    rw [e]
    exact mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun j _ => (hpos j).le) Real.pi_pos.le
  set M : ℂ → ℂ := fun s => ∏' j : J, factor (mass j) (shift j) s
  have hM (s : ℂ) : HasProd (fun j : J => factor (mass j) (shift j) s) (M s) :=
    (multipliable_factor hJ hshift s).hasProd
  have hM0 : M ρ₀ ≠ 0 := tprod_factor_ne_zero hJ hshift fun j =>
    factor_ne_zero hγ₀ (hmin j j.2.1) j.2.2
  have hMc : M (starRingEnd ℂ ρ₀) = starRingEnd ℂ (M ρ₀) := tprod_factor_conj hJ hshift ρ₀
  have hMk (ρ : ℂ) (hρ : ρ ∈ stripZeros) (hre : σ < ρ.re) (h1 : ρ ≠ ρ₀)
      (h2 : ρ ≠ starRingEnd ℂ ρ₀) : M ρ = 0 := by
    refine tprod_of_exists_eq_zero ?_
    rcases lt_or_gt_of_ne (im_ne_zero_of_mem hρ) with h | h
    · refine ⟨⟨starRingEnd ℂ ρ, ⟨conj_mem_stripZeros hρ, by simpa using hre,
        by simpa using h⟩, fun e => h2 ?_⟩, ?_⟩
      · rw [← e]; simp
      · simpa using (factor_self (ρ := starRingEnd ℂ ρ) (by simpa using h)).2
    · exact ⟨⟨ρ, ⟨hρ, hre, h⟩, h1⟩, (factor_self h).1⟩
  have hMn (ρ : stripZeros) : ‖M ρ‖ ≤ Real.exp L := by
    have := hM ρ
    rw [HasProd, SummationFilter.unconditional_filter] at this
    refine le_of_tendsto' this.norm fun F => (Finset.norm_prod_le _ _).trans ?_
    refine (Finset.prod_le_prod (fun j _ => norm_nonneg _) fun (j : J) _ =>
      norm_factor_le (mass_mem _).1 (mass_mem _).2 (div_pos Real.pi_pos (hJ j j.2)).le
        ρ.2.2.2.le).trans ?_
    rw [← Real.exp_sum]
    exact Real.exp_le_exp.2 (hL F)
  -- constants
  obtain ⟨Q, hQ⟩ := exists_arch_bound b
  have hQ0 : 0 ≤ Q := by
    have := (norm_nonneg _).trans (hQ 0)
    rwa [zero_div, Real.exp_zero, mul_one] at this
  set SK := ∑' ρ : stripZeros, (zeroMult ρ : ℝ) * ‖K ρ‖
  have hSK : 0 ≤ SK := tsum_nonneg fun ρ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  set A := K ρ₀ * M ρ₀
  have hA : 0 < ‖A‖ := norm_pos_iff.2 (mul_ne_zero hK hM0)
  set m₀ : ℝ := (zeroMult ρ₀ : ℝ)
  have hm₀ : 0 < m₀ := Nat.cast_pos.2 (WeilExplicit.zeroMult_pos hz₀)
  set a := 2 * m₀ * ‖A‖
  have ha : 0 < a := by positivity
  set c := ‖K 0‖ + Q * Real.exp (L / 2) + Real.exp L * SK + C * R ^ θ
  set T₀ := max (c / (a * (ρ₀.re - σ))) (2 * Real.log 2 + b.rOut) + 1
  refine ⟨Real.exp T₀, fun Y hY ε hε hrun => ?_⟩
  have hY0 : 0 < Y := (Real.exp_pos _).trans_le hY
  have hTY : T₀ ≤ Real.log Y := by rw [← Real.exp_le_exp, Real.exp_log hY0]; exact hY
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεa : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ, cexp (φ * I) = ε := by
    rcases hε with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨π, by simp [exp_pi_mul_I]⟩
  -- a point of the right phase
  set T := Real.log Y + b.rOut
  set x := φ - A.arg - ρ₀.im * T
  set y := toIcoMod Real.two_pi_pos 0 x
  have hy := toIcoMod_mem_Ico Real.two_pi_pos 0 x
  rw [zero_add] at hy
  set t := T + y / ρ₀.im
  have ht1 : T ≤ t := le_add_of_nonneg_right (div_nonneg hy.1 hγ₀.le)
  have ht2 : t ≤ T + 2 * π * (1 / ρ₀.im) := by
    have : y / ρ₀.im ≤ 2 * π * (1 / ρ₀.im) := by
      rw [mul_one_div]; exact div_le_div_of_nonneg_right hy.2.le hγ₀.le
    linarith
  have ht : 2 * Real.log 2 + b.rOut < t := by
    linarith [le_max_right (c / (a * (ρ₀.re - σ))) (2 * Real.log 2 + b.rOut)]
  have ht0 : 0 ≤ t := by linarith [Real.log_pos one_lt_two]
  have htc : c / (a * (ρ₀.re - σ)) < t := by
    linarith [le_max_left (c / (a * (ρ₀.re - σ))) (2 * Real.log 2 + b.rOut)]
  have hphase : cexp (ρ₀ * t) * A = ((Real.exp (ρ₀.re * t) * ‖A‖ * ε : ℝ) : ℂ) := by
    obtain ⟨n, hn⟩ : ∃ n : ℤ, x - y = n * (2 * π) :=
      ⟨toIcoDiv Real.two_pi_pos 0 x, by rw [self_sub_toIcoMod, zsmul_eq_mul]⟩
    have e0 : ρ₀.im * t = ρ₀.im * T + y := by simp only [t]; field_simp
    have e1 : ρ₀.im * t + A.arg = φ - n * (2 * π) := by
      have hx : x = φ - A.arg - ρ₀.im * T := rfl
      linarith
    conv_lhs => rw [cexp_mul_real, ← norm_mul_exp_arg_mul_I A]
    calc _ = Real.exp (ρ₀.re * t) * ‖A‖ * cexp (((ρ₀.im * t + A.arg : ℝ)) * I) := by
          push_cast; rw [add_mul, Complex.exp_add]; ring
      _ = _ := by
          rw [e1]
          push_cast
          rw [show ((φ : ℂ) - n * (2 * π)) * I = φ * I - n * (2 * π * I) by ring,
            Complex.exp_sub, exp_int_mul_two_pi_mul_I, div_one, hφ]
  -- the averaged explicit formula
  set B := C * (R * Y) ^ θ
  have hs : ∀ u ∈ Icc 0 L, -B ≤ ε * smoothDiff b (t + u) := fun u hu =>
    smoothDiff_sign b (mul_nonneg hC (by positivity)) fun z hz => by
      have hz' : z ∈ Icc Y (R * Y) := ⟨by
        calc Y = Real.exp (T - b.rOut) := by
              simp only [T]; rw [add_sub_cancel_right, Real.exp_log hY0]
          _ ≤ Real.exp (t + u - b.rOut) := Real.exp_le_exp.2 (by linarith [hu.1])
          _ ≤ z := hz.1, by
        have h2S := mul_le_mul_of_nonneg_left hS0 (by positivity : (0 : ℝ) ≤ 2 * π)
        calc z ≤ Real.exp (t + u + b.rOut) := hz.2
          _ ≤ Real.exp (Real.log Y + Real.log R) := Real.exp_le_exp.2 (by
              simp only [r, L, T] at *; linarith [hu.2])
          _ = R * Y := by rw [Real.exp_add, Real.exp_log hY0, Real.exp_log hR]; ring⟩
      have := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hY0.le.trans hz'.1) hz'.2 hθ) hC
      linarith [hrun z hz']
  have key := limit_bound b (fun j : J => mass j) (fun j => shift j) (fun j => mass_mem j)
    (fun j => (div_pos Real.pi_pos (hJ j j.2)).le) (M := M) (fun ρ => hM ρ) hL hQ hεa ht hs
  -- the pair `ρ₀, conj ρ₀` against the remaining zeros
  set f : stripZeros → ℂ := fun ρ => (zeroMult ρ : ℂ) * (cexp (ρ * t) * K ρ) * M ρ
  have hf : Summable f := ((summable_norm_lap b).mul_left (Real.exp t * Real.exp L)).of_norm_bounded
    fun ρ => norm_term_le b (hMn ρ) ρ (by nlinarith [ρ.2.2.2])
  set p : stripZeros → ℝ := fun ρ => ε * (f ρ).re
  have hp : Summable p := hf.norm.of_norm_bounded fun ρ => by
    simp only [p]; rw [Real.norm_eq_abs, abs_mul, hεa, one_mul]; exact abs_re_le_norm _
  set z₀ : stripZeros := ⟨ρ₀, hz₀⟩
  set z₁ : stripZeros := ⟨starRingEnd ℂ ρ₀, conj_mem_stripZeros hz₀⟩
  have hz : z₀ ≠ z₁ := fun e => by
    have := congrArg (fun z : stripZeros => (z : ℂ).im) e
    simp [z₀, z₁] at this
    linarith
  have hp0 : p z₀ = m₀ * (Real.exp (ρ₀.re * t) * ‖A‖) := by
    have e : f z₀ = ((m₀ * (Real.exp (ρ₀.re * t) * ‖A‖ * ε) : ℝ) : ℂ) := by
      rw [ofReal_mul, ← hphase]
      simp only [f, z₀, A, m₀]
      push_cast
      ring
    simp only [p]
    rw [e, ofReal_re]
    linear_combination (m₀ * (Real.exp (ρ₀.re * t) * ‖A‖)) * hε2
  have hp1 : p z₁ = p z₀ := by
    have e : f z₁ = starRingEnd ℂ (f z₀) := by
      simp only [f, z₀, z₁, K]
      rw [zeroMult_conj z₀, hMc, lap_conj, map_mul, map_mul, map_mul, map_natCast,
        ← Complex.exp_conj, map_mul, conj_ofReal]
    simp only [p]
    rw [e, conj_re]
  set g : stripZeros → ℝ :=
    fun ρ => Real.exp (σ * t) * Real.exp L * ((zeroMult ρ : ℝ) * ‖K ρ‖)
  have hg : Summable g := (summable_norm_lap b).mul_left _
  have hg0 (ρ : stripZeros) : 0 ≤ g ρ := by
    have := norm_nonneg (K ρ); have : (0 : ℝ) ≤ zeroMult ρ := Nat.cast_nonneg _; positivity
  set P : Finset stripZeros := {z₀, z₁}
  have hcompl : -(Real.exp (σ * t) * Real.exp L * SK) ≤
      ∑' z : ↑((P : Set stripZeros)ᶜ), p z := by
    have h1 (z : ↑((P : Set stripZeros)ᶜ)) : -g z ≤ p z := by
      have hzP := z.2
      simp only [P, Finset.coe_insert, Finset.coe_singleton, mem_compl_iff, mem_insert_iff,
        mem_singleton_iff, not_or] at hzP
      have hne0 : ((z : stripZeros) : ℂ) ≠ ρ₀ := fun e => hzP.1 (Subtype.ext e)
      have hne1 : ((z : stripZeros) : ℂ) ≠ starRingEnd ℂ ρ₀ := fun e => hzP.2 (Subtype.ext e)
      have hb : |p z| ≤ g z := by
        simp only [p]
        rw [abs_mul, hεa, one_mul]
        refine (abs_re_le_norm _).trans ?_
        by_cases hre : σ < ((z : stripZeros) : ℂ).re
        · simp only [f]
          rw [hMk _ (z : stripZeros).2 hre hne0 hne1, mul_zero, norm_zero]
          exact hg0 _
        · exact norm_term_le b (hMn z) z (mul_le_mul_of_nonneg_right (not_lt.1 hre) ht0)
      linarith [neg_abs_le (p z)]
    calc -(Real.exp (σ * t) * Real.exp L * SK) = -∑' z, g z := by rw [tsum_mul_left]
      _ ≤ -∑' z : ↑((P : Set stripZeros)ᶜ), g z :=
          neg_le_neg (Summable.tsum_subtype_le g _ hg0 hg)
      _ = ∑' z : ↑((P : Set stripZeros)ᶜ), -g z := tsum_neg.symm
      _ ≤ _ := Summable.tsum_le_tsum h1 (hg.subtype _).neg (hp.subtype _)
  have hsplit := hp.sum_add_tsum_compl (s := P)
  rw [Finset.sum_pair hz, hp1, hp0] at hsplit
  have hlow : ε * (∑' ρ : stripZeros, f ρ).re = ∑' ρ, p ρ := by
    rw [re_tsum hf, ← tsum_mul_left]
  -- comparison of growth rates
  set E := Real.exp (σ * t)
  have hE1 : 1 ≤ E := Real.one_le_exp (by nlinarith)
  have hEh : Real.exp ((t + L) / 2) ≤ Real.exp (L / 2) * E := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
  have hcE : c * E = ‖K 0‖ * E + Q * Real.exp (L / 2) * E + Real.exp L * SK * E +
      C * R ^ θ * E := by
    simp only [c]; ring
  have hB : B ≤ C * R ^ θ * E := by
    have h1 : 0 ≤ Real.log Y := by
      linarith [Real.log_pos one_lt_two,
        le_max_right (c / (a * (ρ₀.re - σ))) (2 * Real.log 2 + b.rOut)]
    have h2 : Real.log Y ≤ t := by linarith
    have : Real.log Y * θ ≤ σ * t := by
      linarith [mul_le_mul_of_nonneg_left hθσ h1, mul_le_mul_of_nonneg_right h2 (hθ.trans hθσ)]
    show C * (R * Y) ^ θ ≤ C * R ^ θ * Real.exp (σ * t)
    rw [Real.mul_rpow hR.le hY0.le, ← mul_assoc, Real.rpow_def_of_pos hY0]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 this) (mul_nonneg hC (by positivity))
  have hdom := exp_dominates ha hσ₀ htc
  have hK0 := norm_nonneg (K 0)
  have := mul_le_mul_of_nonneg_left hEh hQ0
  have haE : a * Real.exp (ρ₀.re * t) = 2 * (m₀ * (Real.exp (ρ₀.re * t) * ‖A‖)) := by
    simp only [a]; ring
  simp only [f, K] at key hlow
  linarith [mul_le_mul_of_nonneg_left hE1 hK0]

/-! ### A rightmost zero -/

/-- Let `dyadicDiff x ≥ -C x ^ θ` on `[Y, RY]`, or `dyadicDiff x ≤ C x ^ θ` on `[Y, RY]`, for one
fixed ratio `R > 1` and arbitrarily large `Y`. Then either some zero has maximal real part, or
every zero in the critical strip has real part at most `max θ (1/2)`. -/
theorem exists_rightmost_of_bound {R θ C : ℝ} (hR : 1 < R)
    (h : ∀ Y₀, ∃ Y ≥ Y₀, (∀ x ∈ Icc Y (R * Y), -(C * x ^ θ) ≤ dyadicDiff x) ∨
      (∀ x ∈ Icc Y (R * Y), dyadicDiff x ≤ C * x ^ θ)) :
    (∃ ρ₀ ∈ stripZeros, ∀ ρ ∈ stripZeros, ρ.re ≤ ρ₀.re) ∨
      ∀ ρ ∈ stripZeros, ρ.re ≤ max θ (1 / 2) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hcon, ρ₂, h₂, hθ2⟩ := hcon
  have h12 : 1 / 2 < ρ₂.re := (le_max_right _ _).trans_lt hθ2
  classical
  set E := {z : ℂ | z ∈ stripZeros ∧ ρ₂.re ≤ z.re ∧ 0 < z.im}
  let w (z : E) : ℝ := 1 / (z : ℂ).im
  have hw : Summable w := summable_inv_im_of_half_lt h12
  have hsmall : 0 < Real.log R / (3 * π) := div_pos (Real.log_pos hR) (by positivity)
  obtain ⟨F, hF⟩ := ((tendsto_tsum_compl_atTop_zero w).eventually (gt_mem_nhds hsmall)).exists
  let P : Finset ℂ := insert ρ₂ (F.image Subtype.val)
  obtain ⟨p, hp, hmax⟩ := P.exists_max_image re (Finset.insert_nonempty _ _)
  have hθp : max θ (1 / 2) < p.re := hθ2.trans_le (hmax ρ₂ (Finset.mem_insert_self ..))
  have hσ2 : 1 / 2 < p.re := (le_max_right _ _).trans_lt hθp
  have hpZ : p ∈ stripZeros := by
    rcases Finset.mem_insert.1 hp with rfl | h
    · exact h₂
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 h
      exact j.2.1
  let i (z : upper p.re) : {j : E // j ∉ F} :=
    ⟨⟨z, z.2.1, (hmax ρ₂ (Finset.mem_insert_self ..)).trans z.2.2.1.le, z.2.2.2⟩,
      fun hj => z.2.2.1.not_ge (hmax _ (Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem Subtype.val hj)))⟩
  have hi : Function.Injective i := fun _ _ e =>
    Subtype.ext (congrArg (fun j : {j : E // j ∉ F} => ((j : E) : ℂ)) e)
  let v (j : {j : E // j ∉ F}) := w j
  have hv : Summable v := hw.subtype (fun j => j ∉ F)
  have hsum := hv.comp_injective (i := i) hi
  have hle := tsum_comp_le_tsum_of_inj hv (fun j => (one_div_pos.2 j.1.2.2.2).le) hi
  have hW := (lt_div_iff₀' (by positivity : (0 : ℝ) < 3 * π)).1 (hle.trans_lt hF)
  set σ := p.re
  obtain ⟨ρ, hρ, hl⟩ := hcon p hpZ
  obtain ⟨ρ₀, h₀, hmin⟩ := exists_min_im (upper_nonempty hρ hl) hsum
  obtain ⟨Y₀, hY₀⟩ := both_signs hσ2.le (by linarith) (le_max_right θ 0)
    ((max_le_max le_rfl (by norm_num)).trans hθp.le) (le_max_right C 0) h₀
    hmin hsum hW
  obtain ⟨Y, hY, hrun⟩ := h (max Y₀ 1)
  have hle (x : ℝ) (hx : x ∈ Icc Y (R * Y)) : C * x ^ θ ≤ max C 0 * x ^ max θ 0 := by
    have hx1 := (le_of_max_le_right hY).trans hx.1
    exact mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _))
      (Real.rpow_nonneg (by linarith) _) (le_max_right _ _)
  rcases hrun with hrun | hrun
  · exact hY₀ Y (le_of_max_le_left hY) 1 (.inl rfl) fun x hx => by
      linarith [hrun x hx, hle x hx]
  · exact hY₀ Y (le_of_max_le_left hY) (-1) (.inr rfl) fun x hx => by
      linarith [hrun x hx, hle x hx]

/-- If `dyadicDiff x ≥ -C x ^ θ` on `[Y, RY]`, or `dyadicDiff x ≤ C x ^ θ` on `[Y, RY]`, for
one fixed ratio `R > 1`, one exponent `θ < 1` and arbitrarily large `Y`, the trace identity
holds for all tests at some positive width below `1/2`. -/
theorem trace_width_of_bound {R θ C : ℝ} (hR : 1 < R) (hθ : θ < 1)
    (h : ∀ Y₀, ∃ Y ≥ Y₀, (∀ x ∈ Icc Y (R * Y), -(C * x ^ θ) ≤ dyadicDiff x) ∨
      (∀ x ∈ Icc Y (R * Y), dyadicDiff x ≤ C * x ^ θ)) :
    ∃ a, ∃ ha : 0 < a, a < 1 / 2 ∧
      ∀ φ : TestFunction, Trace.HasTrace (Trace.induced ha φ) φ.efFunctional := by
  obtain ⟨β, hβ0, hβ1, hβ⟩ : ∃ β, 0 < β ∧ β < 1 ∧ ∀ ρ ∈ stripZeros, ρ.re ≤ β := by
    rcases exists_rightmost_of_bound hR h with ⟨ρ₀, h₀, hmax⟩ | h'
    · exact ⟨ρ₀.re, h₀.2.1, h₀.2.2, hmax⟩
    · exact ⟨_, lt_max_of_lt_right (by norm_num), max_lt hθ (by norm_num), h'⟩
  have ha : 0 < β / 2 := by linarith
  refine ⟨β / 2, ha, by linarith, trace_eq_efFunctional_of_ne_zero (θ := β) ha (by linarith)
    fun z hz h0 => ?_⟩
  linarith [hβ z ⟨h0, hβ0.trans hz, re_lt_one_of_zero h0⟩]

/-! ### Windows of power length -/

/-- Let `θ ≥ 1/2`. If for arbitrarily large `Y` there is a sign `ε = ±1`, which may depend on `Y`,
with `ε dyadicDiff x ≥ -C x ^ θ` on all of `[Y, Y ^ (1 + δ)]`, then zeta has no zeros to the right
of `θ`. For `θ ≥ 1/2` this contains both one-sided criteria of `Masullo/Dyadic.lean`. The converse
is not asserted. -/
theorem ne_zero_of_dyadic_window {θ δ C : ℝ} (hθ : 1 / 2 ≤ θ) (hδ : 0 < δ)
    (h : ∀ X, ∃ Y ≥ X, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ x ∈ Icc Y (Y ^ (1 + δ)), -(C * x ^ θ) ≤ ε * dyadicDiff x) {ρ : ℂ}
    (hρ : θ < ρ.re) : riemannZeta ρ ≠ 0 := by
  intro hz
  have hs : ρ ∈ stripZeros := ⟨hz, by linarith, re_lt_one_of_zero hz⟩
  set σ := (θ + ρ.re) / 2 with hσdef
  have hσ : 1 / 2 < σ := by linarith
  have hσρ : σ < ρ.re := by linarith
  have hsum : Summable fun z : upper σ => 1 / (z : ℂ).im :=
    (summable_inv_im_of_half_lt hσ).comp_injective
      (i := fun z : upper σ => (⟨z, z.2.1, z.2.2.1.le, z.2.2.2⟩ :
        {ρ : ℂ | ρ ∈ stripZeros ∧ σ ≤ ρ.re ∧ 0 < ρ.im}))
      (fun _ _ e => Subtype.ext (Subtype.mk.inj e))
  obtain ⟨ρ₀, h₀, hmin⟩ := exists_min_im (upper_nonempty hs hσρ) hsum
  obtain ⟨R, hR, hW⟩ : ∃ R : ℝ, 0 < R ∧
      3 * π * ∑' z : upper σ, 1 / (z : ℂ).im < Real.log R :=
    ⟨Real.exp (3 * π * ∑' z : upper σ, 1 / (z : ℂ).im + 1), Real.exp_pos _, by simp⟩
  obtain ⟨Y₀, hY₀⟩ := both_signs hσ.le hR (by linarith : (0 : ℝ) ≤ θ) (by linarith : θ ≤ σ)
    (le_max_right C 0) h₀ hmin hsum hW
  obtain ⟨Y, hY, ε, hε, hw⟩ := h (max (max Y₀ 1) (R ^ (1 / δ)))
  have hY1 : 1 ≤ Y := (le_max_right _ _).trans ((le_max_left _ _).trans hY)
  have hRY : R * Y ≤ Y ^ (1 + δ) := by
    have h2 := Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hY) hδ.le
    rw [← Real.rpow_mul hR.le, one_div_mul_cancel hδ.ne', Real.rpow_one] at h2
    rw [Real.rpow_add (by linarith), Real.rpow_one, mul_comm]
    gcongr
  refine hY₀ Y ((le_max_left _ _).trans ((le_max_left _ _).trans hY)) ε hε fun x hx => ?_
  have h3 := hw x ⟨hx.1, hx.2.trans hRY⟩
  have hx0 : 0 ≤ x ^ θ := Real.rpow_nonneg (by linarith [hx.1]) _
  nlinarith [le_max_left C 0]

end Masullo.Runs
